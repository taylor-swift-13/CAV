# Proof reasoning

## 2026-06-05 initial manual-proof plan for `aug_string_count_index_004`

Phenomenon: after `symexec` succeeded on `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_041101v_aug_string_count_index_004.c`, the generated manual proof file `/home/yangfp/CAV/C/CAV/output/verify_20260605_041101v_aug_string_count_index_004/coq/generated/aug_string_count_index_004_proof_manual.v` contained four `Admitted` obligations: `proof_of_aug_string_count_index_004_entail_wit_1`, `_entail_wit_2_1`, `_entail_wit_2_2`, and `_entail_wit_3`.

Localization: the VC definitions in `/home/yangfp/CAV/C/CAV/output/verify_20260605_041101v_aug_string_count_index_004/coq/generated/aug_string_count_index_004_goal.v` show the exact pattern:

- `entail_wit_1` initializes the invariant by choosing `l1 = nil`, `l2 = l`.
- `entail_wit_2_1` advances one loop step on the branch where the current byte equals `101`, so the prefix count increases by `1`.
- `entail_wit_2_2` advances one loop step on the branch where the current byte is nonzero and not `101`, so the prefix count is unchanged.
- `entail_wit_3` discharges the loop-exit assertion from `s[i] == 0`, which must force `i == n` and the unprocessed suffix to be empty.

Repair action: use the proven shape from nearby string-count examples, adding one helper lemma for the spec on `l ++ [x]`:

```coq
Lemma aug_string_count_index_004_spec_app_single :
  forall (l : list Z) (x : Z),
    aug_string_count_index_004_spec (l ++ x :: nil) =
    aug_string_count_index_004_spec l + (if Z.eq_dec x 101 then 1 else 0).
```

Why this is the right proof structure: the invariant already encodes the exact processed-prefix summary `count = aug_string_count_index_004_spec(l1)`, so the manual proof should only bridge one-step list extension and the exit fact that a zero read cannot occur before index `n`. If these lemmas fail to compile, that will indicate a concrete mismatch in witness shape or hypothesis names; otherwise no annotation change is needed.

## 2026-06-05 exit-proof compile fix for `entail_wit_3`

Phenomenon: compiling `/home/yangfp/CAV/C/CAV/output/verify_20260605_041101v_aug_string_count_index_004/coq/generated/aug_string_count_index_004_proof_manual.v` failed at line 195 with `Found no subterm matching "Zlength (?M ++ ?N)" in H7`. The first version of `proof_of_aug_string_count_index_004_entail_wit_3` copied the nearby string-count pattern too literally and assumed the post-`pre_process` length hypothesis had the same generated name and shape as another workspace.

Localization: `proof_of_aug_string_count_index_004_entail_wit_3` in `.../aug_string_count_index_004_proof_manual.v`, in the branch proving `l2_2` must be empty after establishing `i = n`.

Repair action: replace the direct rewrite on named hypothesis `H7` with a shape-directed argument:

- destruct `l2_2`
- in the non-empty case, match the actual hypotheses `l = app l1_2 (x :: xs)`, `Zlength l1_2 = n`, and `Zlength l = n`
- rewrite the shape fact into the length fact, then use `Zlength_app`, `Zlength_cons`, and `Zlength_nonneg xs` to derive a contradiction

Why this fix is correct: the proof obligation only needs the semantic fact that the suffix length is zero when both the whole list and processed prefix have length `n`. That argument depends on witness content, not on unstable generated hypothesis names, so the proof becomes robust across `pre_process` naming differences.

## 2026-06-05 syntax fix in `entail_wit_3`

Phenomenon: the next `coqc` run failed at line 210 of `.../aug_string_count_index_004_proof_manual.v` with `Syntax error: [ltac_use_default] expected after [tactic]`. The previous patch left a `match goal with ... end` block inside the proof without the terminating tactic punctuation expected by Ltac in that position.

Localization: `proof_of_aug_string_count_index_004_entail_wit_3`, in the local proof of `Hl1_eq_l`.

Repair action: close the `match goal` tactic as `end.` inside the assertion proof block.

Why this fix is correct: the proof term itself is unchanged; only the Ltac block delimiter was malformed.
