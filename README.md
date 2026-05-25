# CAV-JAVA

This repository is configured to use [OpenJML](https://www.openjml.org/) for Java/JML checking.

## Install OpenJML

Install the latest OpenJML release into the local, git-ignored `.tools/openjml` directory:

```bash
./scripts/install-openjml.sh
```

Load the environment in the current shell:

```bash
source ./scripts/env-openjml.sh
```

Verify the installation:

```bash
./scripts/check-openjml.sh
```

## Download Official Examples and Docs

Download/copy OpenJML official resources into `doc/` and `examples/`:

```bash
./scripts/sync-openjml-official-resources.sh
```

The `doc/` directory contains the OpenJML User Guide, the JML Reference Manual,
mirrored documentation/tutorial pages, and release-bundled specs. The `examples/`
directory contains local examples plus official demos, tutorial source examples,
User Guide examples, and mirrored web examples.

## Common Commands

Run ESC checking on a Java file:

```bash
openjml -esc examples/Counter.java
```

Run the guarded OpenJML wrapper used by the end-to-end workflow:

```bash
./scripts/run_openjml_verify.sh examples/Counter.java
```

Prepare a contract workspace without invoking Codex:

```bash
python3 scripts/run_contract.py raw/add_two.md --function-name add_two --dry-run
```

Prepare a verify workspace without invoking Codex:

```bash
python3 scripts/run_verify.py input/add_two.java --class-name AddTwo --dry-run
```

Compile with runtime assertion checking:

```bash
openjml -rac examples/Counter.java
openjml-java -cp examples Counter
```

The installer pins the downloaded release under `.tools/openjml/<version>` and updates `.tools/openjml/current` to point at it.

## Four-Agent Workflow

Per the ICSE 2027 paper, the system has four file-coupled, peer agents:
`contract` (Formalization), `verify` (Verification), `eval` (Evaluation),
`audit` (Audit). `eval` and `audit` are optional reliability components.
Each agent reads immutable inputs from earlier agents, writes its own
artifacts, and is not allowed to modify another agent's outputs.

The Java/OpenJML reusable workflow notes live under `experiences/general/`.
Completed end-to-end example snapshots live under `experiences/end-end/<name>/`.

### contract — formalization

Generates JML pre/postconditions from a natural-language task. Writes
`input/<name>.java` plus a contract workspace under
`output/contract_<ts>_<name>/`.

```bash
python3 scripts/run_contract.py raw/<name>.md --function-name <name>
python3 scripts/run_pipeline.py raw/<name>.md --function-name <name>
python3 scripts/run_pipeline.py raw/<name>.md --function-name <name> --eval
```

### verify — proof construction

Treats the contract as fixed. Adds loop invariants, bridge assertions, and
ghost code until `openjml -esc` accepts the file. Writes a verified working
copy plus a verify workspace under `output/verify_<ts>_<name>/`.

```bash
python3 scripts/run_verify.py input/<name>.java --class-name <ClassName>
python3 scripts/run_pipeline.py input/<name>.java --class-name <ClassName> --only verify
python3 scripts/run_pipeline.py input/<name>.java --class-name <ClassName> --only verify --audit
```

### eval — contract/implementation match (optional)

Screens whether the formalized contract matches the implementation on
concrete cases. Eval treats the JML spec as an executable predicate
(spec-test) and supports `--agent {codex,claude}`. It generates positive and
negative JSON cases, then for each case:

1. substitutes the concrete values into every spec clause and computes the
   boolean mechanically (enumerating bounded `\forall` / `\exists` /
   `\sum` / `\num_of` over the case's range);
2. sends only the clauses it cannot decide mechanically to an LLM-as-judge.

It does not invoke `openjml -esc` and does not re-check well-formedness — the
contract stage's success gate already guarantees the spec parses, type-checks,
and is free of `NOT IMPLEMENTED` / unsupported aggregate quantifiers.

```bash
python3 scripts/run_eval.py input/<name>.java --class-name <ClassName> --agent codex
python3 scripts/run_eval.py input/<name>.java --class-name <ClassName> --agent claude
```

Artifacts land in `output/eval_<ts>_<name>/`. This stage only runs when
`run_pipeline.py` or `run_pipeline_many.sh` is given `--eval`.

### audit — anti-cheating check (optional)

Runs after `verify` reports success. Deterministic checks (in
`scripts/audit_jml.py`) flag contract weakening, vacuous implications
(`requires false`, `false ==> ...`), unproven lemmas (`native`, empty
bodies), `axiom` / `assume` / `Admitted` / `skipesc` / `nowarn`, trivial
postconditions (`ensures true`, `ensures \result == \result`), broad frame
clauses (`assignable \everything`), and reflection / `System.exit`. The
agent then renders findings into an audit verdict
(`VerifiedClean` / `VerifiedWithWarnings` / `NotVerified`). OpenJML is
rerun from the clean audit workspace as a cross-check.

```bash
python3 scripts/run_audit.py --workspace output/verify_<ts>_<name>/                 --agent codex
python3 scripts/run_audit.py --original input/<name>.java --verified <verified>.java --agent claude
```

Artifacts land in `output/audit_<ts>_<name>/`. This stage only runs when
`run_pipeline.py` or `run_pipeline_many.sh` is given `--audit`.

### Default backends

`--agent codex` uses Codex with `gpt-5.4` / medium effort (matching the
paper's default). `--agent claude` uses Claude Code with `sonnet` by default.
Both are exposed via `--model` / `--reasoning-effort` if you need to override
them.

### Batch driver

The pipeline entry runs `contract -> verify` by default. `eval` and `audit`
are both opt-in via flags: `--eval` enables the contract critic, `--audit`
enables the verify critic.

The batch driver is `run_pipeline_many.sh` and uses the same semantics.

```bash
python3 scripts/run_pipeline.py raw/add_two.md --function-name add_two
python3 scripts/run_pipeline.py raw/add_two.md --function-name add_two --eval --audit
./scripts/run_pipeline_many.sh --eval --audit --timeout-seconds 7200 --jobs 1 add_two array_sum
./scripts/run_pipeline_many.sh --no-export-examples --timeout-seconds 7200 --jobs 1 string_length binary_search
```

Successful verify runs are exported to `experiences/end-end/<name>/` by
default; use `--no-export-examples` to disable. Existing same-name examples
are skipped rather than overwritten.
