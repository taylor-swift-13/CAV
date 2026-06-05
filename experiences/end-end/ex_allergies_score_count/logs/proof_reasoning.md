2026-06-05 iteration 1

Phenomenon: `symexec` succeeded, but `/home/yangfp/CAV/C/CAV/output/verify_20260605_063617v_ex_allergies_score_count/coq/generated/ex_allergies_score_count_proof_manual.v` contains six `Admitted` placeholders: `safety_wit_4`, `entail_wit_1`, `entail_wit_2_1`, `entail_wit_2_2`, `entail_wit_3`, and `return_wit_1`.

Location: generated VC in `/home/yangfp/CAV/C/CAV/output/verify_20260605_063617v_ex_allergies_score_count/coq/generated/ex_allergies_score_count_goal.v`.

Repair action: keep the current annotation and prove the remaining goals on the Coq side. The plan is:
- discharge the pure range witnesses with `pre_process; entailer!; lia`;
- add helper lemmas that normalize the mask `(Z.shiftl 1 i) - 1` into low-bit prefixes and prove the two step equations for the set-bit and clear-bit branches;
- use a finite `i = 0 .. 7` split if the generic helper gets brittle, because the loop only ranges over eight concrete bit positions.

Key VC fragments:

```coq
Definition ex_allergies_score_count_entail_wit_2_1 :=
  ...
  “ ((count + 1 ) = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 (i + 1 )) - 1 ))))) ”
```

```coq
Definition ex_allergies_score_count_entail_wit_3 :=
  ...
  “ (count = (ex_allergies_score_count_spec (score_pre))) ”
```

Why this change: the generated goals are pure arithmetic/bit-spec bridges. The VC already carries the loop bounds, parameter immutability, and the prefix-summary invariant, so another annotation rewrite would only shuffle the same proof burden unless the Coq helpers turn out impossible.

2026-06-05 iteration 2

Phenomenon: the first `coqc` pass failed before the semantic lemmas, at `proof_of_ex_allergies_score_count_safety_wit_4`, with:

```text
Attempt to save an incomplete proof
```

and after refining the proof with `cbv [signed_last_nbits]; lia`:

```text
line 28, characters 7-10:
Error: Tactic failure: Cannot find witness.
```

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_063617v_ex_allergies_score_count/coq/generated/ex_allergies_score_count_proof_manual.v`, theorem `proof_of_ex_allergies_score_count_safety_wit_4`.

Repair action: inspect the post-`entailer!` subgoals in `coqtop` and solve the `signed_last_nbits (1 * 2^i) 32` range proof explicitly, instead of assuming `lia` can normalize the bitvector wrapper on its own.

Key proof state fragment:

```coq
BinInt.Z.le INT_MIN
  (signed_last_nbits (1 * 2 ^ i) 32)

BinInt.Z.le
  (signed_last_nbits (1 * 2 ^ i) 32)
  INT_MAX
```

Why this change: this witness is still a pure C-integer safety side condition. Clearing it first keeps the later edits focused on the actual semantic helpers for `entail_wit_2_1`, `entail_wit_2_2`, and `entail_wit_3`.

2026-06-05 iteration 3

Phenomenon: after fixing `safety_wit_4`, recompilation no longer failed immediately, but `coqc` spent more than a minute at 99% CPU inside `proof_manual.v` instead of producing the next theorem error. The only new expensive tactic on that path was `vm_compute` in `proof_of_ex_allergies_score_count_entail_wit_1`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_063617v_ex_allergies_score_count/coq/generated/ex_allergies_score_count_proof_manual.v`, base-case theorem `proof_of_ex_allergies_score_count_entail_wit_1`.

Repair action: remove `vm_compute` and replace it with bounded unfolding / simplification for the concrete zero-mask case, so compilation remains incremental and the first semantic failure is surfaced promptly.

Key command/result fragment:

```text
coqc ... ex_allergies_score_count_proof_manual.v
```

observed as:

```text
99% CPU for > 1 minute, no new stderr; process killed manually
```

Why this change: `vm_compute` can eagerly normalize too much imported infrastructure even when the target arithmetic is tiny. For this workspace, predictable local simplification is more important than maximal reduction.
