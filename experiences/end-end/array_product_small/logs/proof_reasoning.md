2026-06-05 proof iteration 1

Phenomenon: The first generated `proof_manual.v` had four `Admitted` lemmas, but `coqtop` on `array_product_small_return_wit_1` showed the antecedent only contained `IntArray.full a n l` while the goal required `IntArray.full a_pre n_pre l`. That witness was not a pure proof gap; it was missing unchanged-parameter facts from the annotation layer.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_004203v_array_product_small/coq/generated/array_product_small_goal.v`, theorem `array_product_small_return_wit_1`.

Repair action: Go back to annotation, strengthen the invariant with `a == a@pre` and `n == n@pre`, rerun `symexec`, and only then continue manual proof.

Key proof-state fragment after `pre_process`:

```coq
H : i >= n
H1 : i <= n
H2 : ret = product (sublist 0 i l)
============================
IntArray.full a n l |-- “ ret = product l ” && IntArray.full a_pre n_pre l
```

Why this change: The verify workflow requires annotation fixes when the generated VC is semantically under-specified. Rebuilding the VC is cheaper and more correct than inventing an invalid Coq proof for unrelated alias equalities.

2026-06-05 proof iteration 2

Phenomenon: After regenerating the VC, the remaining manual obligations are now the intended ones: one arithmetic bound witness, one initialization entailment, one loop-step entailment, and one return entailment.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_004203v_array_product_small/coq/generated/array_product_small_goal.v`, theorems `array_product_small_safety_wit_3`, `array_product_small_entail_wit_1`, `array_product_small_entail_wit_2`, and `array_product_small_return_wit_1`.

Repair action: Prove the trivial entailments with `pre_process; entailer!; try lia`, and introduce a small local helper for the loop-step equality `product (sublist 0 (i + 1) l) = product (sublist 0 i l) * Znth i l 0`.

Key VC fragment:

```coq
ret = product (sublist 0 i l)
|- (ret * Znth i l 0) = product (sublist 0 (i + 1) l)
```

Why this change: The only nontrivial semantic bridge is the standard “extend prefix by one element” fact. Isolating it as a helper lemma keeps the witness proofs short and stable.
