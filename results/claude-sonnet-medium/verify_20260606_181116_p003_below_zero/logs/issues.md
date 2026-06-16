# Issues Log — p003_below_zero

## Issue 1: entail_wit_1 was already solved by pre_process

**Phenomenon**: After writing `split_pure_spatial` following `pre_process` in the `entail_wit_1` proof, coqc reported "No such goal" at that line.

**Location**: `coq/generated/p003_below_zero_proof_manual.v`, `proof_of_p003_below_zero_entail_wit_1`

**Root cause**: `pre_process` completely solves the invariant initialization goal because all conditions follow trivially (sum(sublist 0 0 l) = 0 is reducible, forall over empty range is vacuous, spatial goals cancel). This is the same pattern as `arr_sum_for_entail_wit_1` in sum_proof_manual.v.

**Resolution**: Replaced the explicit proof steps with just `pre_process.` — the lemma is trivially proved.

## Summary

All 5 manual VCs proved successfully:
- `safety_wit_3`: overflow check using forall hypothesis with sum-split lemmas
- `entail_wit_1`: invariant initialization (solved by pre_process)
- `entail_wit_2`: loop step maintaining invariant and prefix-sum forall
- `return_wit_1`: return 0 case using Left + forall from invariant
- `return_wit_2`: return 1 case using Right + Exists i + sum-split
