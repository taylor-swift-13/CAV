## Round 1

- Phenomenon: `/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_proof_manual.v` contains six admitted obligations after the latest successful `symexec`: `safety_wit_4`, `entail_wit_1`, `entail_wit_2`, `entail_wit_3`, `entail_wit_4`, and `return_wit_1`.
- Location:
  - inner-loop arithmetic preservation: [add_digits_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v:65), [add_digits_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v:186)
  - outer-loop initialization / exit: [add_digits_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v:166), [add_digits_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v:211), [add_digits_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v:230)
- Repair action: reuse the existing `experiences/end-end/digit_sum` proof pattern for the decimal-scan obligations, then add outer-loop helper lemmas for `digital_root_z`.
- Key Coq plan:
  - import the `digit_sum` helper structure: `digit_sum_fuel_nonpositive`, `div_10_lt_pos`, `quot_10_lt_pos`, `rem_10_bounds_pos`, `digit_sum_fuel_stable`, `digit_sum_fuel_stable_ge`, and `digit_sum_z_step`
  - prove `digit_sum_z` fixed on single digits and `digital_root_z` fixed on single digits
  - prove a fuel-stability lemma for `digital_root_fuel`, then derive `digital_root_z_step : 9 < n -> digital_root_z n = digital_root_z (digit_sum_z n)`
  - keep witness proofs short with `pre_process`, `Exists`, `rewrite`, `entailer!`, and `lia`
- Why this plan: the inner loop and the standalone `digit_sum` case share the same semantic equation `digit_sum_z n = n % 10 + digit_sum_z (n ÷ 10)`. The outer loop only adds a second recursion layer over `digit_sum_z`; proving that layer locally in `proof_manual.v` is cheaper and sounder than trying to encode more mathematics back into the C annotations.

## Round 2

- Phenomenon: the first proof draft stalled on helper lemmas, especially `digit_sum_fuel_nonneg`, `digit_sum_fuel_le`, and the `rem`/`mod` and `quot`/`div` bridges.
- Location: [add_digits_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_proof_manual.v:31).
- Repair action: replaced brittle `lia`-only proofs with explicit recursive case splits and arithmetic bridge lemmas:
```coq
replace (n % 10) with (n mod 10) by (symmetry; apply Z.rem_mod_nonneg; lia).
pose proof (Z.div_mod n 10 ltac:(lia)) as Hdecomp.
```
- Why this fixed it: the imported `digit_sum_z` definition is expressed with `Z.rem` and `Z.div`, while the generated C-side witnesses use `%` and `÷`. Coq needed those operators normalized into a common arithmetic shape before the recursive bounds would close.

## Round 3

- Phenomenon: `add_digits_entail_wit_1` from the first strengthened invariant version was false as a pure theorem because it demanded `num_pre <= INT_MAX` from only `0 <= num_pre`.
- Location: [add_digits_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v:155).
- Repair action: returned to annotation, added `num <= INT_MAX by local`, reran `symexec`, and restarted the proof file against the fresh theorem set.
- Key generated change:
```coq
forall (num_pre: Z),
  “ (0 <= num_pre) ” && ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (num_pre <= INT_MAX) ” && ...
```
- Why this fixed it: after the rerun, the range fact was justified from the local `Int` store instead of a false pure premise, so the manual proof only had to discharge the real arithmetic witnesses.

## Round 4

- Phenomenon: the regenerated `proof_of_add_digits_entail_wit_4` still failed because the proof script assumed the wrong branch ordering after `entailer!`.
- Location: [add_digits_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_proof_manual.v:360).
- Repair action: replayed the theorem with `Show.` and matched the exact goal order:
```text
1. sum + num % 10 + digit_sum_z (num ÷ 10) = digit_sum_z n0_2
2. sum + num % 10 <= 2147483647
3. 0 <= sum + num % 10
4. num ÷ 10 <= 2147483647
5. 0 <= num ÷ 10
```
Then reordered the bullets to prove those goals in that order.
- Why this fixed it: once the bullets matched the actual witness order, the existing helper lemmas closed each branch cleanly and no residual goals remained.

## Round 5

- Phenomenon: `proof_of_add_digits_entail_wit_5` initially rewrote the wrong hypothesis after deriving `num = 0`.
- Location: [add_digits_proof_manual.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_proof_manual.v:382).
- Repair action: rewrote `H7 : sum + digit_sum_z num = digit_sum_z n0` with `digit_sum_z 0 = 0`, derived `Hsum0 : sum = digit_sum_z n0`, and then split on `n0 <= 9` versus `9 < n0`:
```coq
replace (digit_sum_z 0) with 0 in H7 by (unfold digit_sum_z; reflexivity).
assert (Hsum0 : sum = digit_sum_z n0) by lia.
```
- Why this fixed it: the exit witness only needs the invariant equality plus either `digit_sum_z_single_digit` or `digital_root_z_step`; rewriting the wrong hypothesis never exposed the required relation `sum = digit_sum_z n0`.
