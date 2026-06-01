---
name: java-openjml-eval
description: Evaluate an existing Java/JML implementation against concrete positive and negative cases by treating the JML spec as an executable predicate (spec-test).
---

Use this workflow independently from contract, verify, and audit. The goal is
to decide whether the JML spec attached to an implementation correctly
characterizes that implementation's behavior on representative inputs. The
spec and the implementation are not modified.

Eval treats the JML spec as an **executable predicate** and looks for cases
where mechanical evaluation disagrees with the implementation. It does **not**
invoke `openjml -esc`, and it does **not** check well-formedness: the contract
stage's success gate already guarantees the spec parses, type-checks, is free
of `NOT IMPLEMENTED` and the unsupported aggregate quantifiers
(`\num_of` / `\sum` / `\product`), and passes the anti-cheating scan. Deductive
proof is the verify/audit stage's job. By the time eval runs, the spec is
already well-formed, so eval only has to test its semantics.

Stage responsibility: eval performs spec-test and the final semantic judge.
Contract runner owns well-formedness, typecheck, unsupported-construct, and
contract-stage anti-cheating gates.


跨阶段共用规则（读写边界、效率、experiences 只读、reasoning log、`Final Result` 格式）见 `skills/COMMON.md`。本文件只描述本阶段特有内容。

## Required References

- `experiences/general/EVAL/README.md`
- `experiences/general/AUDIT/README.md`
- `experiences/general/OPENJML/README.md`

## Inputs

- Implementation/spec Java file.
- Target class and method.
- Workspace path.
- Cases directory and evaluation directory.

## Output Layout

```
output/eval_<timestamp>_<name>/
  original/<name>.java
  cases/cases.json
  evaluation/evaluation.json
  logs/test_reasoning.md
  logs/issues.md
  logs/metrics.md
  logs/final_result.md
  logs/<agent>_prompt_<run>.txt
  logs/<agent>_stdout_<run>.{jsonl,log}
  logs/<agent>_stderr_<run>.log
  logs/<agent>_last_message_<run>.txt
```

## Cases

Generate **exactly the requested number of positive** and **exactly the requested number of negative** cases in
`cases/cases.json`. Positive cases must satisfy every `requires` clause;
their `result` and `post_state` come from running the implementation. Negative
cases either violate one `requires` clause (precondition negative) or claim a
`result` that contradicts the spec (postcondition negative).

Choose cases adversarially: positives must cover EVERY branch / input partition
(e.g. both `a >= b` and `a < b`) and stress each `ensures` clause, so a
one-branch spec bug is not missed because no case hit that branch.

`cases/cases.json` schema:

```json
{
  "class_name": "MaxOfTwo",
  "method_name": "max_of_two",
  "positive": [
    {
      "id": "pos01",
      "description": "a > b on small positives",
      "inputs": {"a": 5, "b": 3},
      "old": {},
      "result": 5,
      "post_state": {}
    }
  ],
  "negative": [
    {
      "id": "neg01_precondition",
      "kind": "precondition",
      "description": "violates requires a >= 0",
      "inputs": {"a": -1, "b": 3},
      "old": {},
      "result": null,
      "post_state": {},
      "violated_clause": "requires a >= 0"
    },
    {
      "id": "neg02_wrong_output",
      "kind": "postcondition",
      "description": "claims wrong result; spec should reject",
      "inputs": {"a": 5, "b": 3},
      "old": {},
      "result": 3,
      "post_state": {},
      "violated_clause": "ensures \\result == a || \\result == b"
    }
  ]
}
```

## Test, then judge only the leftovers

Simple flow: **test each case mechanically; if it cannot be tested
mechanically, judge it.** No separate per-tier files.

1. **Test (mechanical).** For each case, substitute its inputs / `\result` /
   `\old(...)` into every spec clause and compute the boolean by ordinary
   Java arithmetic/logic (`&&`, `||`, `==>`, `<==>`, `!`, constant indexing).
   Enumerate bounded quantifiers over the case's concrete range
   (`\forall` passes iff every witness is true; `\exists` iff some witness is;
   `\sum`/`\num_of`/`\product` by running the implied loop). This is mechanical
   substitution, not judgment — record the `substituted` string and the
   `evaluated` boolean for each clause.
2. **Judge (only leftovers).** A clause that cannot be decided mechanically
   (unbounded quantifier, model function, etc.) is `needs_judge`. Judge those
   clauses, citing the clause and reason. Mechanically decided clauses keep
   their substituted result.

Write ONE results file `evaluation/evaluation.json`:

```json
{
  "cases": [
    {
      "id": "pos01",
      "verdict": "pass",
      "clauses": [
        {"clause": "ensures \\result == a || \\result == b",
         "substituted": "5 == 5 || 5 == 3", "evaluated": true}
      ]
    },
    {
      "id": "pos07",
      "verdict": "needs_judge",
      "clauses": [{"clause": "ensures someModelExpr(\\result)", "substituted": null, "evaluated": null}],
      "judge": {"verdict": "pass", "reason": "..."}
    }
  ]
}
```

`judge` is present only on `needs_judge` cases.

## Aggregate spec verdict

Write `logs/final_result.md` with one of:

- **Spec verdict: Correct** — every positive case passes, every negative case
  fails (as it should), and nothing stayed inconclusive after judging.
- **Spec verdict: Buggy** — at least one positive case failed, or a negative
  case passed. Record the offending cases and clauses.
- **Spec verdict: Inconclusive** — a judged clause stayed undecided. Record
  which clauses prevented a decisive verdict.

## LLM Judge

The spec-test verdict is not enough by itself. Also judge whether the JML spec
soundly and completely characterizes the intended method behavior.

Check all eight items and write `Pass` / `Fail` / `Inconclusive` with a short
reason in `logs/final_result.md`:

- `Precondition strength`: preconditions are not too strong and do not exclude
  valid input cases; the strongest bad form is `requires false`.
- `Postcondition strength`: postconditions are not too weak or trivial and
  actually characterize behavior; the weakest bad form is `ensures true`.
- `Soundness`: every input/output of the correct program satisfies the spec.
- `Positive coverage`: all positive cases satisfy the spec.
- `Parameter coverage`: all input, output, and necessary post-state parameters
  are constrained by the spec.
- `Path coverage`: all method paths / branches are covered.
- `Negative rejection`: all negative cases are rejected by the spec.
- `Completeness`: any implementation satisfying the spec is a correct solution
  to this problem.

Trivial or tautological specs, such as `ensures true` or `ensures \result ==
\result`, must fail this semantic judge unless the raw task is genuinely that
weak.

Vacuous-path specs are also eval responsibilities: `requires false`,
over-strong preconditions that exclude valid inputs, `false ==> P`, and
empty-range quantifiers must fail the semantic judge when they make the spec
unsound or incomplete for the raw task.

Only if all eight items are `Pass`, write:

```text
Judge verdict: Pass
```

If any item fails, write `Judge verdict: Fail`. If any item cannot be decided,
write `Judge verdict: Inconclusive`.

## Eval Integrity

- Generated eval artifacts are ordinary case/evaluation/report files under the
  eval workspace.
- Existing implementation/spec files remain the semantic target being judged.
- Negative cases encode concrete rejected inputs or wrong claimed outputs.
- The verdict is decided by mechanical spec-test plus the semantic judge.

## Experience

Experience is consolidated once at the very end of the flow by
`scripts/experience_consolidate.py`, scoped to whatever flow ran. Eval writes a
clear `logs/final_result.md` and `logs/issues.md` for that consolidation unit
to read.

## Final Result

`logs/metrics.md` must end with one of:

```
Final Result: Success
Final Result: Fail
```

`Final Result: Success` is allowed only when:

- exactly the requested number of positive and negative cases are present in
  `cases/cases.json`;
- `evaluation/evaluation.json` exists and covers every case;
- the aggregated spec verdict is `Correct`;
- `Judge verdict: Pass` is present.

`Spec verdict: Buggy`, `Spec verdict: Inconclusive`, `Judge verdict: Fail`, and
`Judge verdict: Inconclusive` are all treated as `Final Result: Fail`.

If any condition is missing, write `Final Result: Fail`.
