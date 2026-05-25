# Contract Experience

This file records reusable lessons for the contract stage only: turning raw task
text into one Java file with executable code and JML method contracts. It does
not record loop invariants (see `INV.md`), assertions (see `ASSERTION.md`),
helper-lemma proof detail (see `LEMMA.md`), anti-cheating policy (see
`AUDIT.md`), or OpenJML diagnostics in general (see `OPENJML.md`).

常见入口 / symptom index:

- 该写哪些子句、保持题意 -> see 1
- 整数可能溢出 -> see 2
- 数组解引用 / 非空与下标范围 -> see 3
- `NOT IMPLEMENTED ... \num_of` / 计数·求和·求积结果 -> see 4, 7
- contract 阶段要不要写 invariant/assert -> see 5
- 良构门 `check_spec_wellformed.py` 报 fatal -> see 8
- 前置条件设计 -> see 9
- 后置条件设计 / 选择型结果 -> see 10
- frame / `assignable` / `\old` -> see 11
- 表达式良构性 -> see 12
- 安全算术与范围前置 -> see 13
- 异常路径 -> see 14

## 1. 保持题意，写齐 requires/ensures/assignable

- Preserve the intended algorithm and public behavior from the raw task.
- Use JML `requires`, `ensures`, and `assignable` clauses for the target method.
- Keep the contract output free of assumptions, axioms, native methods, or tool
  suppression pragmas (those are anti-cheating violations; see `AUDIT.md`).

## 2. 算术可能超 int 范围时写显式溢出前置条件

Prefer explicit integer overflow preconditions when arithmetic may exceed Java
`int` range. OpenJML uses safe arithmetic for Java code by default and reports
possible overflow/underflow at `+`, `-`, `*`, negation, and casts. State the
range precondition that makes the mathematical result fit (see also 13).

## 3. 数组先要非空，再写下标/长度范围；顺序有意义

For arrays, require non-null arrays and valid length/index ranges before
dereferencing. The order of `requires` clauses matters when a later clause
dereferences an earlier value: write `a != null` before
`0 <= i && i < a.length`. JML treats reference types as non-null by default, but
still write the explicit non-null requirement so the proof obligation is obvious.

## 4. 不要用 `\num_of` / `\sum` / `\product`

- Trigger / symptom: a read-only scan that counts/sums/multiplies elements,
  written with an aggregate quantifier in the postcondition, compiles fine but
  later produces `NOT IMPLEMENTED: ... JML Quantified expression using \num_of`
  (OpenJML `-esc`, exit 6). Confirmed for `\num_of` and `\sum`; `\product` is in
  the same family.
- Root cause: OpenJML's SMT backend cannot translate these aggregate
  quantifiers to SMTLIB, so the obligation can never be discharged downstream
  even though `javac`/typecheck accept it.
- General rule: never put `\num_of`/`\sum`/`\product` in
  `ensures`/`requires`/invariants. Express count/sum/product results with a
  `pure` recursive helper and write the postcondition as `\result == helper(...)`
  (see 7). Use `\forall`/`\exists` for universal/existential properties — those
  are supported and preferred.
- Origin: lesson from `array_count_even`, where a `\num_of` postcondition passed
  the contract compile check and then blocked verify (could not discharge the
  preserved clause, correctly refused to weaken it) and eval (OpenJML exit 6).

## 5. contract 阶段不写 invariant / proof-only assert

Keep contract output free of loop invariants and proof-only assertions unless the
raw task itself includes them — those belong to verify (see `INV.md`,
`ASSERTION.md`). Exception: a `pure` specification helper used by the
postcondition is allowed; it is part of the contract surface, not a proof-only
annotation.

## 6. 用 `pure measured_by` 递归 helper 表达聚合结果

- General rule: define aggregate results (count, sum, max-over-range, product)
  with a `pure` `measured_by` recursive helper, and make the public
  postcondition `\result == helper(...)`. This shape verifies cleanly
  (`openjml -esc` exit 0):

```java
class ArrayCountEven {
    /*@ spec_public @*/
    /*@ private normal_behavior
      @   requires a != null;
      @   requires 0 <= limit && limit <= a.length;
      @   assignable \nothing;
      @   ensures 0 <= \result && \result <= limit;
      @   ensures limit == 0 ==> \result == 0;
      @   ensures limit > 0 ==>
      @       \result == countEvenPrefix(a, limit - 1)
      @               + ((a[limit - 1] % 2 == 0) ? 1 : 0);
      @   measured_by limit;
      @   pure
      @*/
    private static int countEvenPrefix(int[] a, int limit) {
        if (limit == 0) return 0;
        int tail = countEvenPrefix(a, limit - 1);
        if (a[limit - 1] % 2 == 0) return tail + 1;
        return tail;
    }

    //@ requires a != null;
    //@ requires n >= 0;
    //@ requires a.length == n;
    //@ assignable \nothing;
    //@ ensures 0 <= \result && \result <= n;
    //@ ensures \result == countEvenPrefix(a, n);
    public static int array_count_even(int n, int[] a) { /* ... */ }
}
```

## 7. 写聚合 helper 的两个坑

- The helper must be `spec_public` (or `public`). A `private` helper used in a
  `public` method's `ensures` triggers `An identifier with private visibility may
  not be used in a ensures clause with public visibility`.
- Do not write `pure` twice. If `pure` is already inside the JML contract block,
  do not also add a `pure`/`@Pure` annotation, or OpenJML reports
  `Pure is not a repeatable annotation type`.

## 8. contract 阶段的良构门会拦不可证 spec

The contract runner runs `scripts/check_spec_wellformed.py input/<name>.java`
after the anti-cheating scan. It runs `openjml -esc` and classifies output:

- Fatal -> contract fails here: parse/type errors (`: error:`), `NOT IMPLEMENTED`,
  and `\num_of`/`\sum`/`\product`.
- Tolerated -> contract still passes: undischarged verification conditions
  (`Postcondition`/`Invariant`/`Assert`/loop/`ArithmeticOperationRange`/index/
  nullness). Discharging those is the verify stage's job, not contract's.

Run the gate yourself before finishing; exit 1 means fix the spec now (e.g.
rewrite an aggregate with a `pure` recursive helper, see 6), not later. This is
why a `\num_of` spec is caught at contract instead of wasting a full
verify + eval + audit cycle.

## 9. 前置条件描述"方法在何时有定义" (Preconditions.html)

Use `requires` for non-empty collections, non-null inputs, index bounds, divisor
nonzero facts, and integer ranges needed by the implementation. Clause order
matters when a later clause dereferences an earlier value.

## 10. 后置条件说"做什么"，不说"怎么做" (Postconditions.html)

Prefer result properties using `\result` and input/output relations. For
choice-like results, combine membership and ordering facts (e.g. result equals
one candidate and is at least every candidate).

## 11. 显式写副作用与 frame (FrameConditions.html)

Use `assignable \nothing;` for non-mutating methods. For mutating methods, name
only the locations that may change; postconditions over old values use
`\old(...)`. A called method with no precise frame condition can make OpenJML
treat unrelated memory as changed, breaking later assertions.

## 12. 每个 JML 表达式必须良构 (WellDefinedExpressions.html)

Array reads need non-nullness and index bounds; field/method dereferences need
non-null receivers; division and modulo need nonzero divisors. Write contracts so
every `ensures`, `requires`, and quantifier body is itself well-defined.

## 13. 安全算术模式下补范围前置 (ArithmeticModes.html)

OpenJML uses safe arithmetic for Java code by default and reports possible
overflow/underflow; specifications are mathematical by default. Add explicit
range preconditions for `+`, `-`, `*`, negation, and casts when the mathematical
result must fit in Java `int`/`long`.

## 14. 异常路径要么排除、要么显式刻画 (SpecifyingExceptions.html)

If normal execution is intended, add preconditions that exclude null dereference,
division by zero, and bad indexes. If exceptions are part of the task, use
`signals` and `signals_only` rather than leaving exceptional behavior implicit.

## Output

Write `input/<name>.java`, `logs/reasoning.md`, `logs/issues.md`,
`logs/metrics.md`. `reasoning.md` must explain the raw semantics, selected Java
signature, memory/nullness assumptions, integer-range assumptions, and why any
helper method is needed.
