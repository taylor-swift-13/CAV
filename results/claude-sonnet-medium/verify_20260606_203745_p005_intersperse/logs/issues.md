# Issues Log — verify_20260606_203745_p005_intersperse

## Issue 1: symexec "Assign Exec fail" (resolved)

**Gate**: symexec  
**Symptom**: Symexec failed with "Assign Exec fail" on the second array write (`out[k] = numbers[i]`) in the loop body.  
**Root cause**: The single loop invariant covered only the state at the top of the loop (after `out[k] = delimeter`), but the symexec engine required an explicit intermediate assertion between the two writes.  
**Fix**: Added an intermediate `Assert` annotation between `out[k] = delimeter; k++` and `out[k] = numbers[i]; k++` inside the loop body to expose the mid-loop state with `undef_missing_i` shrunk by one step.  
**File**: `annotated/verify_20260606_203745_p005_intersperse.c`

## Issue 2: entail_wit_1 cancel failure (resolved)

**Gate**: coqc proof_manual.v  
**Theorem**: `proof_of_p005_intersperse_entail_wit_1`  
**Symptom**: `cancel (IntArray.seg out_pre 0 1 ...)` failed with "failed to find predicate on either side".  
**Root cause**: After `sep_apply (IntArray.seg_single out_pre 0 ...)`, the LHS had `seg out_pre 0 (0+1) [...]` while the goal RHS had `seg out_pre 0 (2*1-1) [...]`. Both equal 1 but not syntactically equal.  
**Fix**: Added `replace (2 * 1 - 1) with 1 by lia.` after `replace (0 + 1) with 1 by lia.` to normalize both sides.  
**File**: `coq/generated/p005_intersperse_proof_manual.v`

## Issue 3: entail_wit_2/3 sep_apply failure (resolved)

**Gate**: coqc proof_manual.v  
**Theorems**: `proof_of_p005_intersperse_entail_wit_2`, `proof_of_p005_intersperse_entail_wit_3`  
**Symptom**: `sep_apply IntArray.undef_missing_i_to_undef_seg_head.` failed with "Tactic failure: Cannot find witness."  
**Root cause**: The `sep_apply` tactic uses `sepconlistasrts` internally which returned an empty list for this lemma form, preventing the witness search. The lemma has a non-Prop forall (`Z`) before the Prop premise, and `sep_apply`'s internal unification did not find the predicate.  
**Fix**: Replaced `sep_apply` with `sep_apply_l_atomic` providing explicit arguments:
```coq
sep_apply_l_atomic (IntArray.undef_missing_i_to_undef_seg_head out_pre (2 * i - 1) (2 * numbers_size_pre - 1)).
+ dump_pre_spatial. lia.
+ ...
```
`sep_apply_l_atomic` uses `_consume_props_with_subgoal` which correctly generates a subgoal for the `lo < hi` premise and then applies the lemma.  
**File**: `coq/generated/p005_intersperse_proof_manual.v`
