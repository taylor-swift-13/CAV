## 2026-06-05 06:35 CST - Add a parser-stable semantic/safety loop invariant for `digit_product`

Phenomenon: the first `symexec` run failed immediately at the only loop in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_062321v_digit_product.c`:

```text
fatal error: Error: Lack of assertions in some paths for the loop! in /home/yangfp/CAV/C/CAV/annotated/verify_20260605_062321v_digit_product.c:21:4
```

Location: the active annotated copy has no `Inv` before `while (n > 0)`, so symbolic execution has no stable summary relating the shrinking quotient `n`, the accumulator `product`, and the postcondition target `digit_product_z(n@pre)`.

Repair action: introduce a workspace-local helper module `/home/yangfp/CAV/C/CAV/output/verify_20260605_062321v_digit_product/coq/deps/digit_product_helper.v` with parser-facing wrappers

```coq
Definition digit_product_acc_z (n acc : Z) : Z :=
  digit_product_loop_fuel n acc (Z.to_nat n).

Definition digit_product_safe_z (n acc : Z) : Prop :=
  digit_product_safe_fuel n acc (Z.to_nat n).
```

and import them from the annotated C file so the loop invariant can avoid direct `Z.to_nat` syntax inside C annotations. The invariant to add at the loop head is:

```c
/*@ Inv
      0 <= n &&
      0 <= product &&
      digit_product_safe_z(n, product) &&
      digit_product_acc_z(n, product) == digit_product_z(n@pre)
*/
```

Why this shape is appropriate:

- Initialization: after `int product = 1`, current `n` is still `n@pre`. The input precondition `digit_product_pre_z(n)` already gives `0 <= n` and `digit_product_safe_fuel n 1 (Z.to_nat n)`, which is exactly `digit_product_safe_z(n, 1)`. The semantic wrapper satisfies `digit_product_acc_z(n, 1) = digit_product_z(n@pre)` by definition.
- Preservation: under the loop guard `n > 0`, the body computes `product' = product * (n % 10)` and `n' = n / 10`. The helper relation `digit_product_acc_z` matches one recursive step of `digit_product_loop_fuel`, and `digit_product_safe_z` matches one recursive step of `digit_product_safe_fuel`, so the next loop head should keep both the semantic summary and the overflow-safety fact for the next multiplication.
- Exit usability: on loop exit, `!(n > 0)` together with the invariant fact `0 <= n` yields `n == 0`. Then `digit_product_acc_z(0, product)` reduces to `product`, so the invariant should collapse directly to `product == digit_product_z(n@pre)` for the return.
