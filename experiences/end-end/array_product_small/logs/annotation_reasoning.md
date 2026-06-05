2026-06-05 annotation iteration 1

Phenomenon: The active annotated file `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_004203v_array_product_small.c` has no loop invariant for the `for (i = 0; i < n; i++)` scan in `array_product_small`, so `symexec` would not have the prefix-summary fact needed to connect the accumulator `ret` to the postcondition `__return == product(l)`.

Location: function `array_product_small`, the only loop over `i`.

Repair action: Add one loop invariant stating `0 <= i <= n`, `ret == product(sublist(0, i, l))`, and `IntArray::full(a, n, l)`.

Key code fragment:

```c
/*@ Inv
      0 <= i && i <= n &&
      ret == product(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

Why this change: At the loop head, `i` denotes the processed prefix length. Initialization matches because `ret` starts at `1`, which is `product([])`. One loop step multiplies the next array element `a[i]`, so the new accumulator should equal the product of `sublist(0, i + 1, l)`. On exit, `i == n`, so the invariant should collapse directly to the function postcondition while preserving the unchanged array ownership.

2026-06-05 annotation iteration 2

Phenomenon: After the first successful `symexec`, the generated theorem `array_product_small_return_wit_1` in `/home/yangfp/CAV/C/CAV/output/verify_20260605_004203v_array_product_small/coq/generated/array_product_small_goal.v` had antecedent `IntArray.full a n l` but conclusion `IntArray.full a_pre n_pre l`, with no pure facts connecting `a/n` to `a_pre/n_pre`. A direct `coqtop` check after `pre_process` showed those equalities were absent, so the manual VC was semantically under-specified.

Location: loop invariant for `array_product_small`; the unchanged function parameters `a` and `n` were not carried through the loop.

Repair action: Strengthen the loop invariant with explicit unchanged-parameter facts `a == a@pre` and `n == n@pre`, then rerun `symexec` to regenerate cleaner witnesses.

Key code fragment:

```c
/*@ Inv
      0 <= i && i <= n &&
      ret == product(sublist(0, i, l)) &&
      a == a@pre &&
      n == n@pre &&
      IntArray::full(a, n, l)
*/
```

Why this change: The proof guide explicitly warns that unchanged parameter relations should be preserved in the annotation layer, not reconstructed in Coq. These facts are true for this loop because neither `a` nor `n` is assigned. Regenerating the VC should replace an artificial aliasing problem with the intended arithmetic/list proof obligations.
