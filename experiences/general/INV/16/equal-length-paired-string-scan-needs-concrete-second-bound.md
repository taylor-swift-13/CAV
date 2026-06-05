# Equal-length paired string scans should carry the second-read bound explicitly

Date: `2026-06-05`

Symptom:

- The loop scans two read-only null-terminated strings in lockstep.
- The guard or first read is driven by only one side, for example:

```c
while (1) {
    if (a[i] == 0) break;
    if (a[i] != b[i]) d++;
    i++;
}
```

- The contract already states equal logical lengths through an abstract predicate such as `equal_len(la, lb)` or `ex_hamming_distance_pre(la, lb)`.
- But `symexec` still fails at the second read with:

```text
Cannot derive the precondition of Memory Read.
```

Cause:

- At the cutpoint, the frontend can often use the branch fact `a[i] != 0` to justify that `i` is still inside the first string.
- That does not guarantee it will also unfold the abstract equal-length predicate far enough to recover a concrete bound for the second string read.
- If the invariant only keeps the abstract relation, the VC for `b[i]` may be missing a direct arithmetic fact such as `i <= nb`.

Rule:

- For lockstep scans over two read-only equal-length strings or arrays, keep the semantic relation and also keep the arithmetic mirror that the next paired read needs.
- In practice, preserve all three layers together:
  - the prefix-summary semantic invariant;
  - the abstract equal-length relation;
  - concrete arithmetic facts like `na == nb` and `i <= nb`.

Minimal shape:

```c
/*@ Inv
      0 <= i && i <= na &&
      i <= nb &&
      na == nb &&
      count == spec(sublist(0, i, la), sublist(0, i, lb)) &&
      Zlength(la) == na &&
      Zlength(lb) == nb &&
      equal_len(la, lb)
*/
```

Why this is the stable fix:

- `na == nb` and `i <= nb` let `symexec` discharge the immediate safety obligation for the second read without re-deriving it from a higher-level predicate.
- Keeping the abstract relation as well still helps the exit proof and the final semantic bridge.
- This is an annotation-layer repair; do not first detour into proof-only helpers for a VC that fails before fresh witnesses are even generated.

Scope:

- `problem_kind = count`
- `data = string` or read-only arrays
- `pattern = single_loop`
- Single-index paired scans that read `left[i]` and `right[i]` in the same iteration while only one side drives loop progress
