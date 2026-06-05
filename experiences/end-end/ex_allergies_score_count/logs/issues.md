2026-06-05 iteration summary

Phenomenon: the initial annotated file had no loop invariant on the `for (i = 0; i < 8; i++)` loop, so `symexec` stopped at `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_063617v_ex_allergies_score_count.c:21` with:

```text
Error: Lack of assertions in some paths for the loop!
```

Location: annotated C file `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_063617v_ex_allergies_score_count.c`, loop head and loop exit.

Repair action: added a loop invariant

```c
count == ex_allergies_score_count_spec(score & ((1 << i) - 1))
```

plus bounds `0 <= i <= 8`, `0 <= count <= i`, and `score == score@pre`, then added a loop-exit `Assert` for `i == 8` and `count == ex_allergies_score_count_spec(score)`.

Why this change: the function scans the low-bit prefix incrementally, and the masked-prefix spec is the smallest invariant that preserves exactly what the postcondition needs.

2026-06-05 proof debugging

Phenomenon: after `symexec` succeeded, `/home/yangfp/CAV/C/CAV/output/verify_20260605_063617v_ex_allergies_score_count/coq/generated/ex_allergies_score_count_proof_manual.v` contained six admitted lemmas. Early proof attempts failed first on the C-int cast side condition for `1 << i`, then on the masked-prefix semantic equalities, and one compile attempt stalled when `vm_compute` normalized too aggressively in the base case.

Location: generated goals in `/home/yangfp/CAV/C/CAV/output/verify_20260605_063617v_ex_allergies_score_count/coq/generated/ex_allergies_score_count_goal.v`, especially `safety_wit_4`, `entail_wit_2_1`, `entail_wit_2_2`, `entail_wit_3`, and `return_wit_1`.

Repair action:
- proved the cast-range witness with `IntLib.signed_Lastnbits_range`;
- introduced local helper lemmas in `ex_allergies_score_count_proof_manual.v` for:
  - expressing `ex_allergies_score_count_spec` as the sum of eight low-bit testbits for nonnegative inputs;
  - normalizing `score & ((1 << n) - 1)` to `score mod 2^n`;
  - showing `signed_last_nbits (1 << i) 32 = 1 << i` for `0 <= i < 31`;
  - extracting `Z.testbit score i` from the branch masks `score & (1 << i)`;
  - stepping the masked-prefix spec from `i` to `i + 1`;
  - proving the full-prefix equality at `i = 8`;
  - proving the global upper bound `ex_allergies_score_count_spec score <= 8`.
- replaced the stalled `vm_compute` base-case proof with bounded unfolding and targeted rewrites.

Key proof fragments:

```coq
rewrite ex_allergies_score_count_prefix_step by lia.
rewrite Hbit.
simpl.
ring_simplify.
reflexivity.
```

```coq
apply ex_allergies_score_count_spec_le_8.
```

Why this change: the remaining VCs were pure arithmetic / bitvector bridges. Solving them in Coq preserved the verified C implementation and avoided overcomplicating the source annotation.

2026-06-05 final status

Phenomenon: replay compilation generated `.vo/.glob/.aux/.vos/.vok` artifacts under `coq/generated/` and `original/`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_063617v_ex_allergies_score_count/coq/` and `/home/yangfp/CAV/C/CAV/output/verify_20260605_063617v_ex_allergies_score_count/original/`.

Repair action: after `goal.v`, `proof_auto.v`, `proof_manual.v`, and `goal_check.v` all compiled successfully, removed all non-`.v` artifacts from `coq/` and all non-`.c`/`.v` artifacts from `original/`.

Why this change: the verify workflow requires a clean workspace so the runner can replay from source rather than from leftover compiled objects.
