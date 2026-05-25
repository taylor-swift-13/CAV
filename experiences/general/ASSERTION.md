# Assertion Experience

This file records reusable lessons for `Assert` / bridge assertions — local
proof bridges that explain a fact following from the current program state, and
must not replace a missing invariant. It does not record loop-invariant design
(see `INV.md`), lemma encoding (`LEMMA.md`), or general OpenJML diagnostics
(`OPENJML.md`).

常见入口 / symptom index:

- assert 适合做什么 -> see 1
- assert 不该做什么 -> see 2
- assert 是某点的证明义务 / 差一个边界就失败 -> see 3
- 失败先看 failure name -> see 4
- assert 报良构性 -> see 5
- 改 assert 前要记什么 -> see 6

## 1. assert 的好用法

- Bridge a loop-exit fact to a postcondition.
- Expose arithmetic bounds before an operation that OpenJML flags as overflow.
- Split a quantified proof into a smaller local fact.
- Document a case split immediately after an `if` branch.

## 2. assert 的坏用法

- Repeating the postcondition without enough invariants.
- Using an assertion where the only proof is an unchecked assumption.
- Adding assertions to hide an implementation bug.

## 3. assert 是单点证明义务，差一个边界就会失败 (AssertStatement.html)

A JML `assert` is a proof obligation at one program point; OpenJML must prove it
from the current path condition, method contract, loop invariants, and prior
checked facts. Assertions are not part of the public interface — use them for
local proof structure and small bridge facts. An assertion that is almost true
but misses an equality or boundary case will fail: e.g. `neg <= 0` may verify
where `neg < 0` does not, because the zero case is feasible.

## 4. 失败时先归类 failure name (InspectingCounterexamples.html)

Classify the failure name first (`Assert`, `Postcondition`, `Precondition`,
`UndefinedTooLargeIndex`, etc.). It tells you whether the problem is a false
fact, a missing precondition, an undefined expression, or missing loop
information. A temporary `show` statement can expose counterexample values while
debugging, but do not leave debugging-only statements in the final verified file
unless they are part of the intended proof log.

## 5. assert 必须先良构再求真 (WellDefinedExpressions.html)

Assertions must be well-defined before OpenJML can prove their truth. Add bounds
and non-null facts before asserting array contents or object fields.

## 6. 改 assert 前先写 reasoning 日志

Before adding or changing assertions in a verify task, append to
`logs/annotation_reasoning.md`: the OpenJML failure location; the exact assertion
to add; why it follows from existing code and specs; which failure it is expected
to repair.
