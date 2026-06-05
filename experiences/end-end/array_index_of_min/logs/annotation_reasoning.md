## Iteration 1

- Symptom: `symexec` failed with `Error: Lack of assertions in some paths for the loop!` at `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_002314v_array_index_of_min.c:22:4`.
- Location: loop `while (i < n)` in `array_index_of_min`.
- Repair action: add a loop invariant describing `idx` as the first index of the minimum value within the already processed prefix `l[0..i)`, together with bounds `1 <= i <= n` and `0 <= idx < i`.
- Key annotation shape:
  ```c
  /*@ Inv
        1 <= i &&
        i <= n &&
        0 <= idx &&
        idx < i &&
        (forall (j: Z), (0 <= j && j < i) => l[idx] <= l[j]) &&
        (forall (j: Z), (0 <= j && j < idx) => l[j] > l[idx]) &&
        IntArray::full(a, n, l)
  */
  ```
- Why this fix: the loop scans left to right. At each guard point, the processed region is exactly the prefix before `i`. To prove the postcondition on exit, the invariant must already encode that `idx` is the smallest element index in that prefix and that ties are resolved to the earliest occurrence. When the loop exits with `i == n`, the prefix becomes the whole array.

## Iteration 2

- Symptom: after the first proof round, `array_index_of_min_return_wit_1` still needed to transform `IntArray.full a n l` back into `IntArray.full a_pre n_pre l`, and `coqtop` showed no explicit equalities connecting current `a`, `n` to their pre-state versions.
- Location: return witness in `/home/yangfp/CAV/C/CAV/output/verify_20260605_002314v_array_index_of_min/coq/generated/array_index_of_min_goal.v`, sourced from the loop invariant in the annotated C file.
- Repair action: strengthen the loop invariant with unchanged-parameter facts `a == a@pre` and `n == n@pre`.
- Key annotation addition:
  ```c
  a == a@pre &&
  n == n@pre &&
  ```
- Why this fix: the function never mutates the pointer parameter or the array length. Per the proof workflow, this kind of `x` versus `x_pre` mismatch should be repaired at the annotation layer rather than forcing Coq to reconstruct parameter stability from memory predicates.
