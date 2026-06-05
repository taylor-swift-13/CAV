# In-place fill loops need a two-list invariant

Symptom:

- `symexec` succeeds far enough to generate VC, but the loop-preservation or return witness still asks for impossible heap equalities such as proving `IntArray::full ... (replace_Znth i k lr)` from `IntArray::full ... lr`.
- The return witness quantifies both current parameters and `*_pre` parameters, but no longer has the facts needed to relate them.

Cause:

- The invariant uses one logical list for two different roles:
  - the original input contents that the postcondition is stated against;
  - the current mutable heap contents after some prefix has already been overwritten.

After a store like `a[i] = k`, those roles diverge. Reusing one list forces the next VC to pretend the heap did not change.

Rule:

- For overwrite-in-place single-loop array transforms, keep the original list fixed and introduce a second existential list for the current heap.
- Preserve unchanged parameter equalities such as `a == a@pre`, `k == k@pre`, and `n == n@pre` in the invariant when the postcondition is written over pre-state parameters.
- Describe the current heap as:
  - a filled/rewritten prefix in the existential list;
  - an untouched suffix still equal to the original list;
  - `IntArray::full(a, n@pre, lr)` for the concrete mutable heap.

Minimal shape:

```c
/*@ Inv exists lr,
      0 <= i && i <= n@pre &&
      a == a@pre &&
      k == k@pre &&
      n == n@pre &&
      Zlength(lr) == n@pre &&
      (forall (j: Z), (0 <= j && j < i) => lr[j] == k) &&
      (forall (j: Z), (i <= j && j < n@pre) => lr[j] == l[j]) &&
      IntArray::full(a, n@pre, lr)
*/
```

Why this works:

- Before the next loop iteration, the updated heap can choose `replace_Znth i k lr` as the new existential witness.
- The suffix clause supplies the old value exactly at the write boundary before the update.
- On loop exit, `i == n@pre` collapses the untouched suffix and the prefix fact becomes the full postcondition.

Scope:

- single forward loops
- in-place array overwrite/fill/update
- contracts whose postcondition is expressed against the original input list rather than an already-mutated heap witness
