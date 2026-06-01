---
name: java-openjml-audit
description: Audit a verify workspace (or Java/JML file) for anti-cheating violations - contract weakening, unproven lemmas/axioms, suppressions.
---

Use this workflow independently from contract, verify, and eval. The goal is
to detect whether a "verified" Java/JML artifact actually earned its
verification, or whether it relied on cheating constructs that a human
reviewer should reject.

Audit treats the original and verified Java files as read-only inputs. It runs
deterministic scripts to flag proof-bypass patterns and asks the agent to
compile the findings into a single audit verdict.


跨阶段共用规则（读写边界、效率、experiences 只读、reasoning log、`Final Result` 格式）见 `skills/COMMON.md`。本文件只描述本阶段特有内容。

## Pipeline Position

Audit is the fourth and last agent. Inputs are produced by verify; outputs
land in their own workspace next to the verify workspace.

Input forms (the runner accepts either):

- A verify workspace directory: `output/verify_<ts>_<name>/` — audit reads
  `original/<name>.java`, `verified/<name>.java`, and `logs/`.
- A pair of Java files: `--original <orig.java> --verified <verified.java>`.

Output workspace:

```
output/audit_<timestamp>_<name>/
  original/<name>.java          # copy of the contract-stage source
  verified/<name>.java          # copy of the verify-stage source
  audit/
    findings.json               # one entry per detected violation
    findings.md                 # human-readable rendering
  logs/
    reasoning.md
    issues.md
    metrics.md
    final_result.md
    cheating_scan_stdout.log
    cheating_scan_stderr.log
    contract_diff.log           # contract clauses present in original but missing in verified
    openjml_cross_check_stdout.log
    openjml_cross_check_stderr.log
    <agent>_prompt_<run>.txt
    <agent>_stdout_<run>.{jsonl,log}
    <agent>_stderr_<run>.log
    <agent>_last_message_<run>.txt
```

## Detection Categories

The audit script (`scripts/audit_jml.py`) flags violations across these
categories. Each finding has a `category`, a `severity` (`error` | `warning`),
a file path, a line number, and the offending text.

### contract_weakening

A baseline `requires` / `ensures` / `assignable` clause that appears in the
contract-stage source but no longer appears in the verified source. Severity
`error`. Detected by normalized line comparison (the same logic
`check_jml_cheating.py --baseline` already uses).

### unchecked_axiom

The verified source contains the keyword `axiom`. JML/OpenJML supports
`axiom` for user-asserted facts that are accepted without proof. Severity
`error`. Already covered by `check_jml_cheating.py`.

### unproven_lemma

The verified source declares a helper method intended as a lemma but cannot
be checked:

- `native` modifier — no body, no checkable contract;
- empty body (`{}`) on a non-trivial method whose JML asserts a non-trivial
  fact;
- `@*pure` model method with `ensures` but no body;
- method body containing only `//@ assume ...;` followed by a fall-through
  return.

Severity `error` when the method appears in a JML `\old`, `ensures`, or
`assert` context. Severity `warning` when only present in unrelated code.

### assume_or_admitted

Any `//@ assume`, `Admitted`, or `skipesc` in the verified source. Severity
`error`. Already covered by `check_jml_cheating.py`.

### broad_frame_clause

The spec uses an overly broad frame clause that lets the verifier accept
arbitrary mutation:

- `assignable \everything;`
- `modifies \everything;`

Severity `error`. Matches the paper's "broad frame clauses" check.

### nowarn_or_suppression

`nowarn`, `@SuppressWarnings("openjml")`, or analogous suppression that hides
an unsolved obligation. Severity `error`.

### reflection_or_runtime_exit

`Class.forName`, `java.lang.reflect`, `System.exit`. Severity `error`.

## Audit Pipeline

1. The runner copies the original and verified Java files into the audit
   workspace.
2. The runner invokes `scripts/audit_jml.py --baseline <original>
   <verified>` which emits `audit/findings.json`, prints findings to stderr,
   and exits non-zero if any `error`-severity finding is present.
3. The runner runs `scripts/run_openjml_verify.sh <verified>` as a
   cross-check. A passing OpenJML run with `error`-severity audit findings
   is the most damning signal: the proof went through because of cheating.
4. The runner launches the agent (`codex` or `claude`) with the audit skill
   and the findings file. The agent reads the findings, the original spec,
   and the verified source, and writes:
   - `logs/reasoning.md` — per-finding analysis;
   - `audit/findings.md` — human rendering of `findings.json` with
     explanations and remediation;
   - `logs/final_result.md` — overall audit verdict (see below);
   - `logs/issues.md` — list of unresolved questions.

The agent is allowed to mark a finding as `accepted_false_positive` only
when it can cite a JML rule that justifies the construct. False-positive
acceptance must be recorded in `audit/findings.md` per-finding with a
justification.

## Audit Verdict

`logs/final_result.md` records one of:

- **Audit verdict: VerifiedClean** — zero `error`-severity findings remain
  (all flagged items are either absent or accepted as false positives with
  cited justification), and the cross-check OpenJML run passes.
- **Audit verdict: VerifiedWithWarnings** — only `warning`-severity findings
  remain, OpenJML cross-check passes.
- **Audit verdict: NotVerified** — at least one `error`-severity finding is
  not justifiable, or the cross-check OpenJML run fails.

`logs/metrics.md` must end with one of:

```
Final Result: Success
Final Result: Fail
```

`Final Result: Success` is allowed only when:

- `audit/findings.json` exists and parses;
- the agent has written `audit/findings.md` and `logs/final_result.md`;
- the audit verdict is `VerifiedClean` or `VerifiedWithWarnings`;
- the OpenJML cross-check ran (passing or failing — the result is recorded
  even if it contradicts the audit verdict).

`Audit verdict: NotVerified` is treated as `Final Result: Fail`.

## Rules

- Audit uses the implementation, the spec, and the verified file as read-only
  evidence.
- Audit produces reports under `audit/` and `logs/`, then returns a justified
  audit verdict.
- The agent's job is to render the findings into a justified audit verdict.
- The detection pipeline runs even when the agent is offline; the agent
  cannot substitute its own judgment for the deterministic checks.
- Every `error`-severity finding either remains an `error` in the verdict
  or carries an explicit `accepted_false_positive` justification citing a
  specific JML rule.

## Experience

Experience is consolidated once at the very end of the flow by
`scripts/experience_consolidate.py`, scoped to whatever flow ran. Audit writes
clear `audit/findings.md` and `logs/final_result.md` for that consolidation
unit to read.
