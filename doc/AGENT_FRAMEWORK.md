# Java/OpenJML Agent Framework

A closed-loop pipeline that turns a raw task into a machine-checked,
non-cheating JML proof. Two **solver** stages generate artifacts; two **critic**
stages try to overturn them; a final unit consolidates what was learned.

```
raw/<name>.md
   │
   ▼  ┌──────────── contract block ────────────┐
      │ contract solver  ──►  eval critic       │   eval "Buggy" ──► restart contract
      └─────────────────────────────────────────┘   (spec ↔ impl disagreement)
   │  produces input/<name>.java
   ▼  ┌──────────── verify block ──────────────┐
      │ verify solver   ──►  audit critic       │   audit "NotVerified" ──► restart verify
      └─────────────────────────────────────────┘   (proof cheated)
   │  produces verified/<name>.java (OpenJML ESC passes, no cheat)
   ▼
   experience consolidation  ──►  experiences/general/*.md
```

Run it:

```bash
# end-to-end (models/agent come from config/agents.json)
python3 scripts/run_pipeline.py raw/<name>.md --function-name <fn>
python3 scripts/run_pipeline.py raw/<name>.md --function-name <fn> --eval --audit
# a single block:
python3 scripts/run_pipeline.py raw/<name>.md --function-name <fn> --only contract
python3 scripts/run_pipeline.py input/<name>.java --class-name <C> --only verify
```

## Components

### Orchestrator — `scripts/run_pipeline.py`

By default this runs `contract -> verify`. The critic stages are opt-in:
`--eval` enables the contract critic and `--audit` enables the verify critic.
Runs the two blocks **strictly serially**, then consolidation. Bounded by
`--total-budget-seconds` and `--max-overturn-rounds`. `--only contract|verify|all`.
Maps each critic verdict to one of three outcomes:

- `ok` → proceed;
- `overturn` → restart the matching solver with the critic's findings injected
  (`eval Buggy → contract`, `audit NotVerified → verify`);
- `inconclusive` (critic crashed / undecided) → **fail the block** — never a
  silent pass.

### Solver loop — `scripts/agent_loop.py`
Generic budget-driven driver used by both solvers:

- each round gets the *remaining* budget as its timeout;
- a round is restarted **only** when the agent exits early without meeting the
  success gate and budget remains;
- **timeout is failure** — a timed-out round is not restarted;
- restart context (a downstream critic's findings, or the previous round's
  blocker) is appended to `logs/continue.md`; the agent resumes the same
  workspace and writes `logs/summary.md` each round.

### Solvers
- **contract** (`scripts/run_contract.py`): raw task → one Java file with
  impl + JML contract. Success gate = file exists ∧ anti-cheating scan ∧
  **well-formedness gate**.
- **verify** (`scripts/run_verify.py`): repairs the verified working copy
  until OpenJML ESC passes. Success gate = fingerprint ∧ anti-cheating scan ∧
  `openjml -esc` exit 0.

### Critics (single-shot)
- **eval** (`scripts/run_eval.py`, spec-test mode): does the spec characterize
  the impl? Flow = generate cases → mechanically test → judge only what cannot
  be tested mechanically → one `evaluation/evaluation.json` + `Spec verdict:`.
  Single capable model. Treats the impl as the oracle, so it tests the **spec**.
- **audit** (`scripts/run_audit.py`): is the proof a cheat? `audit_jml.py`
  (deterministic regex/diff) + an OpenJML cross-check feed an agent that does the
  **semantic** review (over-strong/contradictory preconditions, non-literal
  vacuity, weak postconditions) and renders `Audit verdict:`. The agent always
  runs — it is the only semantic layer.

### Gates (deterministic, fast)
- `scripts/check_spec_wellformed.py` — contract gate: `openjml -esc` + classify.
  Fatal on parse/type errors, `NOT IMPLEMENTED`, `\num_of`/`\sum`/`\product`;
  **tolerates** undischarged VCs (that is verify's job).
- `scripts/check_jml_cheating.py` — regex anti-cheating scan.
- `scripts/audit_jml.py` — deterministic cheat detector (syntactic only).

### Consolidation — `scripts/experience_consolidate.py`
Runs once at the very end, scoped to whatever ran (contract / verify / all).
Extracts only **general, reusable** lessons into `experiences/general/*.md`,
per-entry (`## N.`), and may write nothing if there is no general lesson.

### Config — `config/agents.json` + `scripts/agent_config.py`
Holds the infrequently-changed settings (agent backend, model names per stage,
CLI binaries, reasoning effort, eval case counts). Precedence:
**CLI flag > config file > built-in default**. Override file with `--config` or
`$CAV_AGENT_CONFIG`.

### Knowledge base — `experiences/`
- `experiences/general/` — per-entry lessons (`CONTRACT.md`, `INV.md`,
  `ASSERTION.md`, `LEMMA.md`, `OPENJML.md`, `EVAL.md`, `AUDIT.md`) + `README.md`
  (entry index + symptom→entry map). Solvers read these by symptom.
- `experiences/end-end/` — completed example snapshots.
- `experiences/INDEX.md` — controlled vocabulary for verify's workspace
  fingerprint.

### Skills — `skills/{contract,verify,eval,audit}/SKILL.md`
The workflow each agent follows; the runner injects the relevant skill into the
agent prompt.

## Design invariants

- **Timeout = failure, never restart on timeout.**
- **A critic that can't decide fails the block** (no silent pass).
- **Audit's semantic review always runs** (deterministic detection is syntactic
  only; never short-circuit the agent away).
- **Experience is general or omitted**, consolidated once at the end, never
  per-stage and never task-specific.
- **Contract blocks unprovable-but-compilable specs** (`\num_of` etc.) up front,
  instead of wasting a full verify+eval+audit cycle.
