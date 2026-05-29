# Audit Policy (Anti-Cheating)

This file records the anti-cheating policy used across stages: verification is
useful only if success is not obtained by weakening the problem or bypassing the
verifier. It does not record invariant/assertion/lemma design (see `../INV/README.md`,
`../ASSERTION/README.md`, `../LEMMA/README.md`) or general OpenJML diagnostics (`../OPENJML/README.md`).

常见入口 / symptom index:

- 禁止项清单 -> see 1
- 扫描器与门禁 -> see 2
- `assume` 为什么危险 -> see 3
- bodyless lemma -> see 4
- "支持" != "可接受" -> see 5
- 空泛证明 / 不可达路径 -> see 6

## 1. 禁止项

- `assume`, especially `assume false`.
- `axiom`, `Admitted`, or similar unchecked proof claims.
- OpenJML suppression pragmas such as `skipesc` or broad `nowarn`.
- Weakening or deleting baseline `requires`, `ensures`, or `assignable` clauses.
- Adding over-strong preconditions that exclude normal inputs.
- Using `native`, reflection, or unchecked helper methods to hide behavior.
- Catching all failures or returning constants just to satisfy the postcondition.
- Marking a negative eval case as successful when OpenJML does not report the
  expected failure.

## 2. 扫描器与门禁

`scripts/check_jml_cheating.py` scans Java files and, in verify mode, compares a
verified file against the original input contract. The verify wrapper must fail
if the scanner fails. Scanner success is required before `Final Result: Success`.

## 3. `assume` 让验证器无证接受谓词 (AssumeStatement.html)

A JML `assume` tells the verifier to accept a predicate without proof; it can
make invalid code verify, especially when the assumed predicate is false on a
feasible path. It may be useful only as a temporary proof-development sketch —
this workflow forbids it in final contract, verify, and eval artifacts. Never
replace a missing loop invariant, precondition, or lemma with `assume`.

## 4. 以 `;` 结尾的 lemma 是未证假设 (Lemmas.html)

A lemma declaration ending with `;` is not proved by OpenJML; treat it like an
unchecked assumption (this workflow accepts no external proof). A proved lemma
must have a body and must verify in the same OpenJML run as the target code.

## 5. "OpenJML 支持" 不等于 "本工作流可接受" (features.shtml.html)

OpenJML supports constructs such as `axiom`, `nowarn`, `spec_public`, `ghost`,
`model`, and `pure`, but support does not make every construct acceptable here.
Suppression features (`nowarn`, `skipesc`) and unchecked facts (`axiom`, unproved
model methods, bodyless lemmas) bypass the evidence we need from OpenJML and are
forbidden.

## 6. 空泛证明也算作弊 (InitiallyConstraint.html)

Vacuous proofs can arise when inconsistent assumptions make a path impossible.
Treat impossible preconditions and contradictory invariants as cheating even when
OpenJML exits successfully.
