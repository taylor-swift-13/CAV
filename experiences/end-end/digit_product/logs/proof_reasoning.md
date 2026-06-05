## 2026-06-05 06:42 CST - Prove the helper-based loop witnesses directly

Phenomenon: after the first successful `symexec`, the generated manual proof file `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/coq/generated/digit_product_proof_manual.v` contains five admitted obligations:

```coq
proof_of_digit_product_safety_wit_5
proof_of_digit_product_entail_wit_1
proof_of_digit_product_entail_wit_2
proof_of_digit_product_return_wit_1
proof_of_digit_product_return_wit_2
```

Location and VC shape from `digit_product_goal.v`:

- `digit_product_safety_wit_5` needs the multiplication bound `INT_MIN <= product * (n % 10) <= INT_MAX` under `digit_product_safe_z n product` and `n > 0`.
- `digit_product_entail_wit_1` initializes the invariant from the precondition and therefore needs `digit_product_pre_z n_pre` to imply `digit_product_safe_z n_pre 1` and `digit_product_acc_z n_pre 1 = digit_product_z n_pre`.
- `digit_product_entail_wit_2` is the loop-preservation VC: it must derive the next-state nonnegativity, recursive safety, and semantic equality for `(n / 10, product * (n % 10))`.
- `digit_product_return_wit_1` collapses the helper invariant at loop exit using `n <= 0` and `0 <= n`.
- `digit_product_return_wit_2` handles the early-return branch `n_pre == 0`.

Repair action: keep the current annotation and prove these VCs in `proof_manual.v` by adding helper lemmas that expose one recursive step of the imported definitions:

```coq
digit_product_loop_fuel_stable
digit_product_safe_fuel_stable
digit_product_acc_z_step
digit_product_safe_z_step
```

Why this is the right layer:

- The VCs already have the right semantic facts; no witness is asking for missing program-state information such as an omitted parameter-equality or missing loop-exit assertion.
- The hard part is only Coq-side normalization of the fuelled definitions `digit_product_loop_fuel` and `digit_product_safe_fuel`, exactly the kind of pure proof bridge that should stay in `proof_manual.v`.
- The step proofs need the standard decimal facts `0 <= n / 10 < n` and `0 <= n % 10 <= n` for positive `n`; these are pure helper lemmas, not annotation changes.
