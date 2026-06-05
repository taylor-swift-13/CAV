# Annotation Reasoning

## Iteration 1: add prefix-count invariant for the read-only negative-count scan

Program point: the initial annotated file had a bare single-line loop at [verify_20260604_233715v_array_count_negative.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260604_233715v_array_count_negative.c:20):

```c
for (int i = 0; i < n; i++) if (a[i] < 0) count++;
```

Symexec failed with:

```text
Error: Lack of assertions in some paths for the loop!
```

Localization: the failure is at the only loop head in `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_233715v_array_count_negative.c:20`. The contract already gives `0 <= n`, `Zlength(l) == n`, and `IntArray::full(a, n, l)`. The loop only reads `a[i]`, conditionally increments `count`, and must preserve the full array resource while returning the number of negative elements in the whole list.

Fix action: add a loop-head invariant that states:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_negative_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
```

and add a minimal exit assertion after the loop:

```c
/*@ Assert
      i == n &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_negative_spec(l) &&
      IntArray::full(a, n, l)
*/
```

Why this shape: at the `for` control point, `i` is the next array index to inspect, so `sublist(0, i, l)` is exactly the processed prefix. The accumulator should therefore equal `array_count_negative_spec` of that prefix. `a == a@pre` and `n == n@pre` keep the unchanged-parameter facts available for generated witnesses instead of forcing Coq to reconstruct them later. `IntArray::full(a, n, l)` is preserved because the loop only reads the array. On exit, the failed guard gives `i >= n`; combined with `i <= n` from the invariant this yields `i == n`, and with `Zlength(l) == n` the prefix becomes the whole list.

## Iteration 2: fix loop-invariant attachment syntax for `for`

Phenomenon: after the first edit, symexec rejected the annotation with:

```text
Expected loop after loop invariant.
```

Localization: `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_233715v_array_count_negative.c:28`. The first attempt placed the `/*@ Inv ... */` block between the `for (...)` header and the loop body while also declaring `i` inside the `for`. That placement does not match the accepted front-end syntax for `for` loops in this toolchain.

Fix action: move `int i;` to the enclosing block, place `/*@ Inv ... */` immediately before the `for`, and keep the same invariant body. This matches the stable pattern used in `QualifiedCProgramming/QCP_examples/QCP_demos_human/sum.c`.

Why this fixes the issue: the verifier parses `for` invariants as annotations attached to the upcoming loop statement, not as annotations inserted between the loop header and body. Hoisting `i` also keeps it in scope for the post-loop `Assert`.

## Iteration 3: restore the original executable loop shape for source-integrity replay

Phenomenon: the runner audit reported:

```text
Source integrity gate failed:
- annotated C changes executable implementation after removing comments/QCP annotations
```

Localization: `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_233715v_array_count_negative.c`. The current annotated version had changed the executable tokens from the input's single-line loop

```c
for (int i = 0; i < n; i++) if (a[i] < 0) count++;
```

to a different implementation shape with a separate `int i;`, a block loop body, and a post-loop assertion that survives comment stripping as a changed control-flow skeleton.

Fix action: move back to the exact original executable statement sequence:

```c
int count = 0;
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre &&
      n == n@pre &&
      count == array_count_negative_spec(sublist(0, i, l)) &&
      IntArray::full(a, n, l)
*/
for (int i = 0; i < n; i++) if (a[i] < 0) count++;
return count;
```

Why this shape: the source-integrity gate compares executable code after removing QCP annotations. Keeping the original `for (int i = 0; ... ) if (...) count++;` token sequence preserves the implementation exactly while still attaching the loop invariant at the correct control point for symexec. The post-loop semantic fact `count == array_count_negative_spec(l)` should be recovered from the regenerated exit witness instead of by changing executable structure.
