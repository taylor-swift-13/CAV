# Cheating Checks

This repo uses two separate checks because they catch different problems.

## 1. Artifact Check

Script:

```bash
python3 scripts/check_verify_audit.py
```

Purpose: inspect finished verification workspaces for proof bypasses, contract
changes, artifact-shape issues, and generated-file tampering.

It checks:

- each workspace has the expected original C, annotated C, and four target
  generated Coq files;
- annotated C does not change executable code after stripping comments/QCP
  annotations;
- annotated C does not weaken or change the original function contract;
- `proof_manual.v` contains no `Admitted`, `admit`, `Abort`, or `give_up`;
- `proof_manual.v` does not introduce `Axiom`, `Hypothesis`, `Parameter`, or
  `Conjecture`;
- `proof_manual.v` imports stay within known QCP/Coq namespaces;
- when given a fresh symexec output directory, `goal.v`, `proof_auto.v`, and
  `goal_check.v` match fresh runner-generated output. `proof_manual.v` is the
  only target file allowed to contain manual edits.

Example:

```bash
python3 scripts/check_verify_audit.py results/codex/gpt-5.4/high/verify_x
python3 scripts/check_verify_audit.py --json --no-fail results/codex/gpt-5.4/high
```

Automatic runner output:

- `logs/verify_audit.json`: concise structured artifact audit:
  `ok`, `summary`, `inputs`, and categorized `findings`.
- `logs/audit_check_coqc.log`: verbose QCP mirror symexec/coqc/final-check log for
  debugging only.

This script does not inspect what the agent read while working.

## 2. Transcript / Workspace Access Check

Script:

```bash
python3 scripts/check_leakage.py
```

Purpose: inspect `agent_stdout_*.jsonl` tool calls for reading answer sources or
other workspaces.

Default target:

```bash
results/claude/ark-code-latest/api
```

Run on the default Ark result directory:

```bash
python3 scripts/check_leakage.py
```

Run on a specific result root or workspace:

```bash
python3 scripts/check_leakage.py results/claude/ark-code-latest/api
python3 scripts/check_leakage.py output/verify_20260617_1256531247_p076_is_simple_power
```

Machine-readable output:

```bash
python3 scripts/check_leakage.py --json results/claude/ark-code-latest/api
```

The script exits nonzero when findings are present. Use `--no-fail` for a
report-only run.

### What Counts As Cheating

The transcript check flags actual agent tool calls that read or enumerate:

- `ground_truth*` mirrors;
- `results/`;
- another `output/verify_*` workspace;
- `annotated_input/`;
- repo-level `annotated/verify_*`;
- another `QualifiedCProgramming/QCP_examples/CAV/verify_*` workspace;
- another `QualifiedCProgramming/SeparationLogic/examples/CAV/verify_*`
  workspace;
- wildcard or parent-directory scans under QCP CAV workspace roots, such as
  `find SeparationLogic/examples/CAV` or `grep ... QCP_examples/CAV/*/...`.

The current QCP mirror workspace is allowed. By default, reads of the current
`output/verify_*` workspace are also allowed because runner logs may refer to it.
Use this stricter mode to flag current-output reads as well:

```bash
python3 scripts/check_leakage.py --strict-current-output output/verify_...
```

### Recommended Workflow

After a batch finishes:

```bash
python3 scripts/check_leakage.py results/claude/ark-code-latest/api
```

For any finding, remove or quarantine the corresponding result directory before
counting model success.

Before starting a new batch, remove stale QCP CAV mirrors so agents cannot see
old workspaces:

```bash
find QualifiedCProgramming/QCP_examples/CAV \
     QualifiedCProgramming/SeparationLogic/examples/CAV \
     -maxdepth 1 -mindepth 1 -type d \
     \( -name 'verify_*' -o -name 'ground_truth*' \) -print
```

Delete stale entries only when no active run owns them.
