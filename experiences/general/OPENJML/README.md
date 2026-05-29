# OpenJML Experience

This file records reusable lessons about running OpenJML and reading its
diagnostics, across all stages. It does not record contract spec shapes (see
`../CONTRACT/README.md`), invariant design (`../INV/README.md`), assertion use (`../ASSERTION/README.md`),
lemma encoding (`../LEMMA/README.md`), or anti-cheating policy (`../AUDIT/README.md`).

常见入口 / symptom index:

- 怎么跑 ESC -> see 1
- public spec 引用 private 字段 -> see 2, 9
- 算术溢出 -> see 3
- 循环证明失败 -> see 4
- `\num_of` / `\sum` 部分实现 -> see 5
- `assignable` 失败 -> see 6
- exit 0 是否就算成功 -> see 7
- `PossiblyNullDeReference` 等运行期检查名 -> see 8
- nullness 失败 -> see 10
- 看反例 -> see 11

## 1. 运行 ESC

```bash
./scripts/run_openjml_verify.sh input/example.java
```

Direct:

```bash
source ./scripts/env-openjml.sh
openjml -esc input/example.java
```

## 2. Visibility 失败：public spec 不能引用 private 字段

A public spec cannot reference a private field unless the field is `spec_public`
or exposed through a model field. See 9 for the manual detail.

## 3. 算术溢出失败

Add explicit range preconditions or prove intermediate bounds (see
`../CONTRACT/README.md` 13).

## 4. 循环证明失败

Add bounds, accumulator, frame, and exit-useful invariants (see `../INV/README.md`).

## 5. 计数/求和量词只是部分实现

`\num_of` and `\sum` are only partially implemented in OpenJML. If a preserved
baseline contract uses them, first prove the executable loop state with supported
invariants or pure helpers; if the only remaining failure is the quantified
clause itself, record a tool-support blocker instead of weakening the contract.
(Best avoided entirely at contract time — see `../CONTRACT/README.md` 4.)

## 6. `assignable` 失败

Use `assignable \nothing;` for pure read-only methods and precise locations for
mutating methods.

## 7. exit 0 是必要非充分条件

OpenJML exit code 0 is necessary but not sufficient. The anti-cheating scanner
must also pass (see `../AUDIT/README.md`).

## 8. 运行期安全检查会以验证失败出现 (checks.shtml.html)

- Java runtime safety checks appear as verification failures. Common names:
  `PossiblyNullDeReference`, `PossiblyNegativeIndex`, `PossiblyTooLargeIndex`,
  `PossiblyDivideByZero`, `PossiblyNegativeSize`, and arithmetic/range checks.
- JML proof failures name the violated obligation, such as `Precondition`,
  `Postcondition`, `Invariant`, `Assert`, or loop-related obligations. Use the
  failure name to choose whether to strengthen a contract, invariant, assertion,
  or implementation.

## 9. Specification 可见性随 Java 可见性 (Visibility.html)

A public spec cannot mention a private field unless it is made visible for
specifications, e.g. with `spec_public`, or hidden behind a model field. Prefer
`spec_public` for small examples with simple private fields; use model fields
only when the public abstraction differs meaningfully from the representation.

## 10. JML 引用默认非空 (Nullness.html)

References are non-null by default; nullable values require explicit `nullable`
annotations or command-line/default settings. On a nullness failure, decide
whether the API should reject null (`requires x != null`) or support it.

## 11. 反例检查是调试辅助 (InspectingCounterexamples.html)

The first diagnostic often gives the obligation class and source location; the
associated declaration points back to the spec clause that generated the
obligation. Counterexample inspection is a debugging aid; final success still
requires checked specifications and no forbidden proof shortcuts.
