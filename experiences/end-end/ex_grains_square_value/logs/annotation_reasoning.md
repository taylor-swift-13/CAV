## 2026-06-05 08:11:19 CST

Phenomenon: `ex_grains_square_value` contains a `for (i = 1; i < square; i++)` loop in [annotated/verify_20260605_080500v_ex_grains_square_value.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_080500v_ex_grains_square_value.c:1) but has no loop invariant yet, so `symexec` cannot justify the accumulator state across iterations.

Location: target function `ex_grains_square_value`, loop over local variables `i` and `value`.

Repair action: add one loop invariant before the `for` loop capturing the real control point state: `1 <= i <= square`, `square == square@pre`, and `value == power_nonnegative_z(2, i - 1)`.

Key code shape:

```c
/*@ Inv
      1 <= i &&
      i <= square &&
      square == square@pre &&
      value == power_nonnegative_z(2, i - 1)
*/
for (i = 1; i < square; i++) {
    value *= 2;
}
```

Why this change: after initialization, `i == 1` and `value == 1 == 2^(1-1)`, so the invariant initializes cleanly. Under the loop guard `i < square`, the contract's quantified bound covers both `2^(i-1)` and `2^i`, and after `value *= 2; i++`, the next loop-head state becomes `value == 2^(i-1)` again. On exit, `!(i < square)` plus `i <= square` yields `i == square`, which matches the postcondition directly.
