2026-06-05 symbolic execution and proof issues

Issue 1
Phenomenon:
The annotated file initially had no loop invariant, so there was no preserved relation linking the changing locals `count` and `n` back to the postcondition.
Location:
`/home/yangfp/CAV/C/CAV/annotated/verify_20260605_055926v_count_set_bits.c`, loop `while (n > 0)`.
Fix:
Added the invariant
```c
0 <= n &&
n <= n@pre &&
0 <= count &&
count + count_set_bits_z(n) == count_set_bits_z(n@pre)
```
and a loop-exit assertion carrying the same summary to the return site.
Why:
This matches the implementation structure: each iteration consumes one low bit and divides `n` by 2, so the stable quantity is “counted bits so far + bits remaining in current `n`”.

Issue 2
Phenomenon:
The first manual-proof attempt used a helper that recursively unfolded one more step on `n / 2`, which produced the wrong target shape for the branch-preservation proofs.
Location:
`/home/yangfp/CAV/C/CAV/output/verify_20260605_055926v_count_set_bits/coq/generated/count_set_bits_proof_manual.v`, helper area above the witness proofs.
Fix:
Replaced that helper with a stronger well-founded lemma `count_set_bits_fuel_irrelevant` over `Z.to_nat n`, then derived `count_set_bits_fuel_enough` and the one-step spec equation `count_set_bits_z_step`.
Why:
The generated VC needs “any sufficient fuel gives the same recursive result”, not repeated unfolding of the recursive call itself.

Issue 3
Phenomenon:
Multiple `coqc` iterations failed because `entailer!` produced a different subgoal order than the initial script assumed, and some goals were already discharged before trailing rewrites ran.
Location:
Witness proofs `proof_of_count_set_bits_safety_wit_6`, `proof_of_count_set_bits_entail_wit_1`, `proof_of_count_set_bits_entail_wit_2_1`, `proof_of_count_set_bits_entail_wit_2_2`, `proof_of_count_set_bits_return_wit_1`.
Fix:
Used iterative replay plus `coqtop` inspection to identify the actual subgoal shapes, then:
- removed dead script after `entailer!` where the goal was already closed;
- kept remainder facts in the `%` notation emitted by the VC;
- solved the remaining quotient bounds with `Z.quot_pos` and `Z.quot_le_upper_bound`.
Why:
Once the semantic step equation and branch fact are present in context, the remaining obligations are only quotient-range side conditions. Matching the real proof-state order made the scripts stable.

Final Result: Success
