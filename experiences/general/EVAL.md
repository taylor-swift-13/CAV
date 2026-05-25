# Eval Experience

This file records reusable lessons for the eval stage — testing whether the JML
spec attached to an implementation correctly characterizes that implementation's
behavior, by treating the spec as an executable predicate (spec-test). It does
not record contract spec shapes (see `CONTRACT.md`) or anti-cheating policy
(`AUDIT.md`).

Eval does **not** invoke `openjml -esc` and does **not** check well-formedness:
the contract stage's success gate already guarantees the spec parses,
type-checks, and is free of `NOT IMPLEMENTED` / `\num_of` / `\sum` / `\product`.
By the time eval runs the spec is well-formed; eval only tests its semantics.

常见入口 / symptom index:

- 要生成多少 case、什么形式 -> see 1
- 正例怎么写 -> see 2
- 反例怎么写 -> see 3
- 正/反例与前置条件 -> see 4
- 正/反例与后置条件·断言 -> see 5
- 机械求值 vs 交给 judge -> see 6
- 异常路径 -> see 7
- 工作区布局 -> see 8
- 终判条件 -> see 9
- 反作弊 -> see 10

## 1. 生成具体 case 到 cases.json

Generate the requested number of positive and negative concrete cases into
`cases/cases.json`. A case is concrete data (`inputs`, `old`, `result`,
`post_state`), not a JUnit test and not an OpenJML harness. Positive `result` /
`post_state` come from running the implementation; the implementation is the
oracle, so what is under test is the **spec**.

Choose cases adversarially: positives must cover EVERY branch / input partition
(e.g. both `a >= b` and `a < b`) and stress each `ensures` clause, so a
one-branch spec bug is not missed because no case exercised that branch.

## 2. 正例

Use legal concrete inputs that satisfy every `requires`; exercise boundary
values, normal values, and small structural cases. Record the actual `result` /
`post_state` produced by the implementation. A positive case is expected to
make every spec clause evaluate true.

```json
{"id": "pos01", "description": "a > b", "inputs": {"a": 5, "b": 3},
 "old": {}, "result": 5, "post_state": {}}
```

## 3. 反例

Be deterministic and concrete; target one failure per case. Two kinds:

- **precondition negative** — violate exactly one `requires` clause; record
  `violated_clause`. Do not violate several unrelated requirements at once.
- **postcondition negative** — legal inputs but a `result` / `post_state` that
  contradicts the spec; the spec, evaluated mechanically, should reject it.

```json
{"id": "neg02_wrong_output", "kind": "postcondition",
 "inputs": {"a": 5, "b": 3}, "old": {}, "result": 3, "post_state": {},
 "violated_clause": "ensures \\result == a || \\result == b"}
```

A negative case that mechanically evaluates to "spec satisfied" is an eval
failure (the spec failed to reject a wrong claim).

## 4. 正/反例与前置条件 (Preconditions.html)

Positive cases must satisfy every `requires` clause, including well-definedness
prerequisites such as non-null arrays and valid indexes. Precondition negatives
should violate one clear precondition only.

## 5. 正/反例与后置条件·断言 (Postconditions.html)

Positive cases should make the target `ensures` clauses evaluate true on the
implementation's real output, not on unstated implementation details.
Postcondition negatives flip one fact directly tied to the method's spec.

## 6. 机械求值优先，judge 只兜底剩下的

For each case substitute its values into every spec clause and compute the
boolean by ordinary arithmetic/logic; enumerate bounded quantifiers
(`\forall` / `\exists` / `\sum` / `\num_of` / `\product`) over the case's
concrete range. Record `substituted` + `evaluated` per clause. Only a clause
that cannot be decided mechanically (unbounded quantifier, model function) is
`needs_judge` — judge those, and do not judge what was already decided
mechanically.

## 7. 异常路径要和真正的 spec 违例区分开 (SpecifyingExceptions.html)

If the target spec intentionally allows exceptional behavior, distinguish
expected exceptional paths from genuine spec violations. Otherwise prefer
ordinary precondition-violation and wrong-output cases.

## 8. 工作区布局

For a target `input/Foo.java`:

```text
output/eval_<timestamp>_foo/
  original/Foo.java
  cases/cases.json
  evaluation/evaluation.json
  logs/test_reasoning.md
  logs/issues.md
  logs/metrics.md
  logs/final_result.md
```

## 9. 终判条件

Eval must write `logs/final_result.md` (the `Spec verdict:` line) and
`logs/metrics.md`. `Final Result: Success` is allowed only when: exactly the
requested number of positive and negative cases are present in `cases.json`;
`evaluation/evaluation.json` exists and covers every case; and the aggregated
verdict is decisive (`Spec verdict: Correct` or `Spec verdict: Buggy`).
`Spec verdict: Inconclusive` (a judged clause stayed undecided) is treated as
`Final Result: Fail`.

## 10. 反作弊

Do not use `assume`, `axiom`, `skipesc`, `nowarn`, unreachable-path tricks, or
impossible helper preconditions; do not weaken or delete the target spec; do not
invoke `openjml -esc` to decide the verdict. (See `AUDIT.md`.)
