# Invariant Experience

This file records reusable lessons for loop-invariant design — the main OpenJML
proof aid for iterative Java code. It does not record `Assert`/bridge detail
(see `../ASSERTION/README.md`), helper-lemma encoding (`../LEMMA/README.md`), or general OpenJML
diagnostics (`../OPENJML/README.md`).

常见入口 / symptom index:

- invariant 的四类内容 -> see 1, 4
- 数组循环 -> see 2, 6
- 终止性 / `decreases` -> see 3
- invariant 写在哪个控制点、用什么语法 -> see 5
- invariant/assert 报 `UndefinedNegativeIndex` 等良构性 -> see 7
- 对象不变式 / 类不变式 -> see 8

## 1. 一条 invariant 的四个角色

- Bound invariant: track the loop variable range, e.g. `0 <= i && i <= n`.
- Frame invariant: state what parts of arrays/objects remain unchanged.
- Accumulator invariant: relate the current accumulator to a prefix or processed
  segment.
- Exit usefulness: ensure invariant plus loop negation implies the
  postcondition.

## 2. 数组循环的 invariant

- State array non-nullness before any indexed access.
- Use quantified formulas over processed and unprocessed ranges.
- Separate read-only preservation from modified-prefix facts.

## 3. 终止性：必要时加 `decreases`

Add `decreases` when OpenJML cannot infer loop progress. The decreases
expression must be non-negative at loop entry and strictly decrease on every
iteration.

## 4. 每个循环通常都需要一份循环规格 (Loops.html)

OpenJML does not infer the full effect of a loop body from all iterations. A
useful loop specification has four parts:

- index bounds, including the exit value;
- an inductive progress fact describing what has been processed so far;
- a loop frame condition for locations modified by the loop;
- a termination measure.

## 5. 语法：`maintaining` / `loop_invariant` / `loop_writes`

OpenJML accepts `maintaining` as loop-invariant syntax; this project also uses
`loop_invariant` when clearer — keep the style consistent within a file. Use
`loop_writes` (or the local equivalent) when a loop writes arrays or object
fields: if a loop mutates `a[i]`, the frame should mention the array region
rather than rely on a method-level frame alone.

## 6. 典型数组循环模式

```java
//@ maintaining 0 <= i && i <= a.length;
//@ maintaining (\forall int k; 0 <= k && k < i; a[k] == k);
//@ loop_writes i, a[*];
//@ decreases a.length - i;
for (int i = 0; i < a.length; i++) {
    a[i] = i;
}
```

## 7. invariant 在入口/保持/退出处都必须良构 (WellDefinedExpressions.html)

For an invariant mentioning `a[k]`, first establish `a != null` and quantified
bounds for `k`. If OpenJML reports `UndefinedNegativeIndex` or
`UndefinedTooLargeIndex` at an invariant or assertion, strengthen bounds before
adding algebraic facts.

## 8. 对象不变式要被构造器和方法出口重建 (Invariants.html)

Object invariants are assumed in method pre-states and must be re-established by
constructors and method exits. Do not introduce a class invariant unless every
relevant constructor and mutating method can preserve it. Public invariants that
mention private fields require a visibility solution such as `spec_public` or a
model abstraction.
