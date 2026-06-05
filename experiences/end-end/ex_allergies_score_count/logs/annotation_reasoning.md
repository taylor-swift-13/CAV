2026-06-05 iteration 1

Phenomenon: `symexec` failed immediately on the loop in [verify_20260605_063617v_ex_allergies_score_count.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_063617v_ex_allergies_score_count.c:21) with `Error: Lack of assertions in some paths for the loop!`.

Location: loop head of `for (i = 0; i < 8; i++)` in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_063617v_ex_allergies_score_count.c`.

Repair action: add a loop invariant that models `count` as the specification applied to the already-processed low-bit prefix, represented by the mask `(1 << i) - 1`, while also carrying the loop bounds and unchanged parameter fact `score == score@pre`. Add a loop-exit `Assert` that instantiates the invariant at `i == 8` so the return witness can target the postcondition directly.

Key code/log fragment:

```text
fatal error: Error: Lack of assertions in some paths for the loop!
```

Planned invariant shape:

```c
/*@ Inv
      0 <= i && i <= 8 &&
      score == score@pre &&
      0 <= count && count <= i &&
      count == ex_allergies_score_count_spec(score & ((1 << i) - 1)) &&
      emp
*/
```

Why this change: the loop processes bit positions `0 .. i-1` and never mutates memory. Masking by `(1 << i) - 1` isolates exactly that processed prefix in a form already expressible with the exported spec symbol, so the exit case `i == 8` should collapse to the required full 8-bit count.
