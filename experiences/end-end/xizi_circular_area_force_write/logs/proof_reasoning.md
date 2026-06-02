## 2026-06-02 Initial proof pass

Symptom: `coq/generated/xizi_circular_area_force_write_proof_manual.v` is entirely `Admitted`, while `Mode: proof-only` forbids changing the C/contract/annotation and requires discharging only the generated manual VCs.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_goal.v`, witnesses `safety_wit_1` .. `safety_wit_16`, `partial_solve_wit_1` .. `partial_solve_wit_7`, and `return_wit_1` .. `return_wit_4`.

Action: start with the shortest proof skeleton from `experiences/general/PROOF/README.md §3`: use `pre_process; entailer!; lia` for pure arithmetic safety obligations, `pre_process; cancel` style proofs for `partial_solve_wit_*`, and explicit `Exists` witnesses for `return_wit_*` matching the generated `IntArray.full` lists.

Key VC fragments:

```coq
xizi_circular_area_force_write_safety_wit_5
|-- “ ((data_length_pre - (area_length_pre - (Znth 1 l 0))) <= INT_MAX) ”
```

```coq
xizi_circular_area_force_write_return_wit_1
|-- EX lr, ... && IntArray.full state_pre 3 lr
```

Why this change: the generated VCs are branch-local arithmetic/list obligations over already-materialized arrays; they should be provable without changing upstream artifacts, and a compile-first pass will expose exactly which witnesses need extra rewrites or helper lemmas.

## 2026-06-02 Return witness refinement

Symptom: compiling `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_proof_manual.v` failed at theorem `proof_of_xizi_circular_area_force_write_return_wit_1` with `Attempt to save an incomplete proof`.

Location: theorem `xizi_circular_area_force_write_return_wit_1` in `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_goal.v`, inspected with `coqtop Show` after `pre_process; Exists ...; entailer!`.

Key proof state:

```coq
goal 2:
  force_pre <> 0 ->
  Znth 0 (replace_Znth 0 ... (replace_Znth 2 1 (replace_Znth 1 ... l))) 0 =
  Znth 1 (replace_Znth 0 ... (replace_Znth 2 1 (replace_Znth 1 ... l))) 0

goal 4:
  Znth 1 l 0 + data_length_pre = area_length_pre ->
  Znth 1 (...) 0 = 0
```

```coq
Locate "%".
Notation "x % y" := (Z.rem x y) (default interpretation)
```

Fix action: rewrite the return witnesses to use the generated `%` term directly, then discharge the remaining list goals with `Zlength_replace_Znth`, `Znth_replace_Znth_Same`, and `Znth_replace_Znth_Diff`. For the modulo branch, use `Z.rem_small` on the strict-less case and `Z.rem_same` on the equality case; for the wrapped branch, rewrite `data_length_pre - (area_length_pre - Znth 1 l 0)` to `Znth 1 l 0 + data_length_pre - area_length_pre` by `lia`.

Why this change: the previous proof used `mod`, which does not match the generated `sac` notation `% = Z.rem`; that left even the spatial self-entailment unsolved. The remaining goals are all explicit same-index/different-index rewrites through nested `replace_Znth`, so a structured bullet proof is the stable fix.

## 2026-06-02 Final blocker before stopping

Symptom: after adding local `replace_Znth` helpers and making `return_wit_1` explicit, `coqc` advanced to `proof_of_xizi_circular_area_force_write_return_wit_2` and failed again with `Cannot find witness`.

Location:
- file: `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_proof_manual.v`
- theorem: `proof_of_xizi_circular_area_force_write_return_wit_2`
- line 215, characters 38-41

Key failing fragment:

```coq
rewrite Znth_replace_Znth_Same by lia.
rewrite Znth_replace_Znth_Diff by lia.
rewrite Znth_replace_Znth_Diff by lia.
rewrite Znth_replace_Znth_Same by lia.
```

Diagnosis: this theorem still uses the old implicit rewrite style, while `return_wit_1` only started compiling after introducing an explicit local alias `w` and spelling out each `Znth_replace_Znth_*` rewrite with the concrete intermediate list. The same inference problem remains here.

Why stopping with `Fail`: `proof_manual.v` still does not compile, so the machine gate for `goal_check.v` cannot even start. Per proof-only mode, I cannot change the C/contract/annotation to bypass the VC, and the current run has not completed the required explicit rewrite conversion for the remaining return witnesses.

## 2026-06-02 Retry attempt 2: explicit rewrite conversion

Symptom: the audit failure is still rooted at `proof_of_xizi_circular_area_force_write_return_wit_2`, where `coqc` reports `Cannot find witness` on the first `rewrite Znth_replace_Znth_Same by lia.` after `entailer!`.

Location:
- file: `/home/yangfp/CAV/OS/CAV/output/verify_20260602_212502v_xizi_circular_area_force_write/coq/generated/xizi_circular_area_force_write_proof_manual.v`
- theorem: `proof_of_xizi_circular_area_force_write_return_wit_2`
- neighboring theorems likely affected by the same pattern: `return_wit_3`, `return_wit_4`

Key generated VC fragment:

```coq
xizi_circular_area_force_write_return_wit_2
|-- EX lr,
   ... “ ((((Znth 1 l 0) + data_length_pre ) > area_length_pre) ->
           ((Znth 1 lr 0) = (((Znth 1 l 0) + data_length_pre ) - area_length_pre ))) ”
```

Fix action: keep the same existential witness, but introduce a local alias `w := data_length_pre - (area_length_pre - Znth 1 l 0)` and rewrite each `Znth` through the concrete nested `replace_Znth` stack using the local lowercase helper lemmas at the top of the file:

```coq
rewrite (Znth_replace_Znth_diff 1 0 w 0
  (replace_Znth 2 1 (replace_Znth 1 w l))) by ...;
rewrite (Znth_replace_Znth_diff 1 2 1 0
  (replace_Znth 1 w l)) by ...;
rewrite (Znth_replace_Znth_same 1 w 0 l) by lia.
```

Why this change: the uppercase library rewrite lemmas leave `coqc` to infer the intermediate list and index-range side conditions by unification, which is exactly where the proof fails. Spelling out the intermediate list makes those obligations syntactic, and the arithmetic branch reduces to `lia` because `w = Znth 1 l 0 + data_length_pre - area_length_pre`.
