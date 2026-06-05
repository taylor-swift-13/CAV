2026-06-05 iteration 1

Phenomenon:
The annotated working copy had the function contract but no loop invariant or loop-exit assertion for `while (n > 0)`, so `symexec` would have no preserved relation connecting the evolving locals `count` and `n` to the postcondition `__return == count_set_bits_z(n@pre)`.

Location:
`/home/yangfp/CAV/C/CAV/annotated/verify_20260605_055926v_count_set_bits.c`, function `count_set_bits`, loop `while (n > 0)`.

Repair action:
Add a loop invariant expressing:
- `0 <= n <= n@pre`
- `0 <= count`
- `count + count_set_bits_z(n) == count_set_bits_z(n@pre)`

Also add a loop-exit `Assert` fixing `n <= 0` after the loop and restating the invariant facts so the return site can target the postcondition directly.

Key code shape:
```c
/*@ Inv
      0 <= n &&
      n <= n@pre &&
      0 <= count &&
      count + count_set_bits_z(n) == count_set_bits_z(n@pre)
*/
while (n > 0) { ... }
```

Why this change:
The implementation consumes one low bit per iteration and replaces `n` by `n / 2`. The natural preserved quantity is “bits already counted + bits still present in the remaining `n`”. This is the smallest invariant likely to make the exit state collapse to `count == count_set_bits_z(n@pre)` once `n <= 0` implies `count_set_bits_z(n) = 0`.
