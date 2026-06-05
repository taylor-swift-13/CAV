2026-06-03 Round 1

Phenomenon: Fresh `symexec` on the annotated file generated four manual theorems in `xizi_bitmap_highest_prio_proof_manual.v`: `entail_wit_1`, `entail_wit_2`, `return_wit_1`, and `return_wit_2`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_{goal,proof_manual}.v`.

Fix action: Reduce the proof burden to three reusable bit-level bridges:
1. `bitmap & (1 << i) = 0` plus `0 <= i` implies `Z.testbit bitmap i = false`.
2. `bitmap & (1 << i) <> 0` plus `0 <= i` implies `Z.testbit bitmap i = true`.
3. `((bitmap >> k) & 1) = 0` plus `0 <= k` implies `Z.testbit bitmap k = false`.

Key VC fragments:

```coq
“ ((Z.land bitmap_pre (Z.shiftl 1 i)) = 0) ”
“ ((Z.land bitmap_pre (Z.shiftl 1 i)) <> 0) ”
“ forall (k: Z), ... -> ((Z.land (Z.shiftr bitmap_pre k) 1) = 0) ”
```

Why this change: The generated VCs are fundamentally about mapping C bitwise facts into the contract’s `Z.testbit` characterization. Once those bridges are available, the loop-preservation and return witnesses should collapse to short arithmetic and first-order proofs.

2026-06-03 Round 2

Phenomenon: `coqc` failed in the first helper lemma with `Found no subterm matching "Z.land ?x (Z.ones ?n)" in H.` The rewrite target was `Z.land x 1`, so `Z.land_ones` could not match structurally.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:29`.

Fix action: Normalize the mask constant before rewriting by changing `1` to `Z.ones 1`, then apply `Z.land_ones`.

Key proof fragment:

```coq
change 1 with (Z.ones 1) in H.
rewrite Z.land_ones in H by lia.
```

Why this change: The helper is still proving the same parity fact; this is only a proof-term normalization so the standard library lemma applies.

2026-06-03 Round 3

Phenomenon: The next `coqc` failure in the same helper was `Cannot find witness` on `assert (x mod 2 = 0) by lia.` After rewriting with `Z.land_ones`, the hypothesis is `x mod 2 ^ 1 = 0`, which `lia` does not normalize automatically through exponentiation.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:32`.

Fix action: Reduce `2 ^ 1` to `2` explicitly before reusing the hypothesis.

Key proof fragment:

```coq
replace (2 ^ 1) with 2 in H by reflexivity.
```

Why this change: This turns the parity helper into a direct rewrite over `x mod 2`, which is exactly the shape consumed by `Z.bit0_eqb`.

2026-06-03 Round 4

Phenomenon: `coqc` advanced into `testbit_false_land_shiftl_eq0` and then failed because `Z.pow2_bits_false` expects the side condition `i <> n`, while the local branch hypothesis was `n <> i`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:64`.

Fix action: Supply the symmetry explicitly with `congruence`.

Key proof fragment:

```coq
rewrite Z.pow2_bits_false by congruence.
```

Why this change: The theorem application was otherwise correct; only the equation orientation blocked rewriting.

2026-06-03 Round 5

Phenomenon: The same helper then stopped on a non-simplified boolean goal: after rewriting the mask bit away, the target became `(Z.testbit x n && false)%bool = false`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:65`.

Fix action: Reduce the boolean connective explicitly with `rewrite Bool.andb_false_r`.

Why this change: This keeps the helper proof direct and stable instead of relying on `simpl` to fire inside the rewritten `Z.land_spec` term.

2026-06-03 Round 6

Phenomenon: `coqc` reached the range helper and failed with `The reference UINT_MAX was not found in the current environment.` The generated goal elaborates the bound, but `UINT_MAX` itself is not available as a standalone Coq identifier inside the manual file.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:102`.

Fix action: State the helper over the concrete unsigned bound `2 ^ 32 - 1` instead of naming `UINT_MAX`.

Why this change: The proof only needs the 32-bit magnitude bound, not the symbolic C macro name. Using the elaborated numeric form matches what the generated VC already carries.

2026-06-03 Round 7

Phenomenon: `coqc` then failed in the high-bit case of `bitmap_zero_from_range_and_cleared_bits` because I used the wrong direction of `Z.log2_lt_pow2`. The proof needs to derive `Z.log2 bitmap_pre < 32` from `bitmap_pre < 2 ^ 32`, not the converse.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:106`.

Fix action: Switch from `proj1` to `proj2` on `Z.log2_lt_pow2`.

Why this change: This aligns the helper proof with the actual implication direction required by `Z.bits_above_log2`.

2026-06-03 Round 8

Phenomenon: The same line still failed because `Z.log2_lt_pow2` is curried over the positivity premise: after partial application it has shape `0 < bitmap_pre -> (bitmap_pre < 2 ^ 32 <-> ...)`, so taking `proj2` before supplying positivity is ill-typed.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:106`.

Fix action: Prove `0 < bitmap_pre` first, instantiate `Z.log2_lt_pow2` with that fact, then use `proj2`.

Key proof fragment:

```coq
assert (Hpos : 0 < bitmap_pre) by lia.
apply (proj2 (Z.log2_lt_pow2 bitmap_pre 32 Hpos)).
exact Hltpow.
```

Why this change: This matches the exact type of the library lemma and keeps the high-bit branch on the standard `bits_above_log2` path.

2026-06-03 Round 9

Phenomenon: `coqc` then reported that the high-bit branch still did not match `Z.bits_above_log2`: for target bit `n >= 32`, the lemma needs `Z.log2 bitmap_pre < n`, while the proof only established `Z.log2 bitmap_pre < 32`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:107`.

Fix action: First derive `Hlog2lt32`, then conclude `Z.log2 bitmap_pre < n` using `n >= 32`.

Why this change: This keeps the bit-zero proof purely arithmetic once the standard `log2` bound is available.

2026-06-03 Round 10

Phenomenon: The `Hlog2lt32` subproof still failed because I inverted the `<->` projection convention. In Coq, `proj1` on `A <-> B` gives `A -> B`, which here is exactly `bitmap_pre < 2 ^ 32 -> Z.log2 bitmap_pre < 32`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:108`.

Fix action: Use `proj1` after supplying the positivity hypothesis.

Why this change: This restores the correct implication direction for the `log2` bound used by `Z.bits_above_log2`.

2026-06-03 Round 11

Phenomenon: After adding the pre-loop `by local` bridge and rerunning `symexec`, the manual witness set shrank to the three real semantic obligations: `entail_wit_3`, `return_wit_1`, and `return_wit_2`. The init/range witnesses are now discharged automatically.

Location: regenerated `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_{goal,proof_manual}.v`.

Fix action: Rebase the manual proof script onto the new VC set and keep only the reusable bit helpers plus proofs for those three theorems.

Why this change: This is the intended division of labor. The annotation layer now handles source-type range extraction; the manual layer only translates bitwise facts into the imported Coq spec.

2026-06-03 Round 12

Phenomenon: `coqc` next failed in `entail_wit_3` because `destruct H as [-> | Hik]` hit the wrong autogenerated hypothesis after `entailer!`. The proof was depending on an unstable Coq name.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:118`.

Fix action: Name the arithmetic case split explicitly as `Hcase` before destructing it.

Why this change: It makes the manual proof robust against witness-local hypothesis renumbering and naming changes.

2026-06-03 Round 13

Phenomenon: Inspecting `entail_wit_3` in `coqtop` showed the stable post-`entailer!` context explicitly:

```coq
H  : Z.land bitmap_pre (Z.shiftl 1 i) = 0
H0 : i >= 0
H5 : forall k : Z, i < k < 32 -> Z.land (Z.shiftr bitmap_pre k) 1 = 0
```

The previous script was still trying to apply the helper lemma to `H0`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:119`.

Fix action: Use `H` as the masked-bit-zero hypothesis and `H5` as the quantified higher-bit hypothesis.

Why this change: This matches the actual VC shape instead of guessing hypothesis positions.

2026-06-03 Round 14

Phenomenon: `entail_wit_3` still failed because the proof needed the converse bridge from `Z.land bitmap_pre (Z.shiftl 1 i) = 0` to `Z.testbit bitmap_pre i = false`, while the helper block only contained the direction from `testbit = false` back to `land = 0`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:119`.

Fix action: Add `land_shiftl_eq0_testbit_false` and use it directly in `entail_wit_3`; define the nonzero helper by contradiction against that new lemma.

Why this change: The generated VCs use the masked C expression as the primary fact, so the proof layer needs a forward translation from that shape into the spec’s `Z.testbit` view.

2026-06-03 Round 15

Phenomenon: The new helper `land_shiftl_eq0_testbit_false` compiled almost completely but stopped on the final boolean normalization step: after rewriting, the hypothesis had shape `(Z.testbit x i && true) = false`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:82`.

Fix action: Rewrite with `Bool.andb_true_r` before concluding.

Why this change: This preserves the direct bit-level argument and avoids introducing extra case splits.

2026-06-03 Round 16

Phenomenon: `entail_wit_3` then failed in the `k = i` branch because, after proving `Z.testbit bitmap_pre i = false`, the target stayed in the generated C-bit shape `Z.land (Z.shiftr bitmap_pre i) 1 = 0`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:136`.

Fix action: Add a dedicated helper `testbit_false_shiftr_land1_eq0` that converts `Z.testbit x k = false` back into the shifted-mask equation.

Why this change: The preservation witness is stated over the generated bitwise expression, so the proof needs both directions of the `testbit`/`((x >> k) & 1)` bridge.

2026-06-03 Round 17

Phenomenon: The next `coqc` pass failed before reaching any new proof obligation because the helper order was wrong: `testbit_false_shiftr_land1_eq0` referenced `testbit_false_land_shiftl_eq0` before it was defined.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:62`.

Fix action: Reorder the helper lemmas so the general `testbit_false_land_shiftl_eq0` is defined before the shifted-mask specialization.

Why this change: This is a pure declaration-order fix; it does not change any proof content.

2026-06-03 Round 18

Phenomenon: `coqtop` showed that after `entailer!`, `return_wit_2` is already reduced to the pure goal `xizi_bitmap_highest_prio_spec bitmap_pre i`. The previous script used `right; repeat split` without first unfolding the spec, so Coq tried to split the wrong outer structure.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:176`.

Fix action: `unfold xizi_bitmap_highest_prio_spec` first, then prove the right disjunct explicitly.

Why this change: The return proof should follow the imported spec’s exact disjunction/product shape rather than relying on generic splitting.

2026-06-03 Round 19

Phenomenon: Even after unfolding the spec, `repeat split` in `return_wit_2` produced a more fine-grained subgoal order than the bullet script assumed, so the `testbit = true` proof was being applied to an arithmetic side goal.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v:177`.

Fix action: Replace `repeat split` with explicit nested `split` steps matching the actual state from `coqtop`.

Why this change: It makes the proof structure stable and keeps each bullet aligned with one semantic conjunct.
