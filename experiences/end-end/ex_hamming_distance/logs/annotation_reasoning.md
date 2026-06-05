2026-06-05 08:xx initial annotation pass

Phenomenon: [annotated/verify_20260605_080838v_ex_hamming_distance.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_080838v_ex_hamming_distance.c) had the executable loop but no `Inv` or exit bridge, so `symexec` would have no preserved summary for `d` and `i`.

Location: function `ex_hamming_distance`, the `while (1)` loop that scans `a[i]` and compares `a[i]` with `b[i]`.

Repair action: model the loop state as a processed prefix. The invariant keeps:
- `0 <= i && i <= na` so the current index is inside the logical string or exactly at the terminator.
- `d == ex_hamming_distance_spec(sublist(0, i, la), sublist(0, i, lb))` so the accumulator is the mismatch count of the processed prefix.
- `Zlength(la) == na && Zlength(lb) == nb` and `ex_hamming_distance_pre(la, lb)` so the equal-length fact remains available at loop exit.

Key annotation shape:
```c
/*@ Inv
      0 <= i && i <= na &&
      d == ex_hamming_distance_spec(sublist(0, i, la), sublist(0, i, lb)) &&
      Zlength(la) == na &&
      Zlength(lb) == nb &&
      ex_hamming_distance_pre(la, lb)
*/
```

Why this change: the program is a single left-to-right scan whose only mutable state is the index and mismatch counter. A prefix-summary invariant matches initialization (`i = 0`, `d = 0`), one-step preservation after either keeping or incrementing `d`, and loop exit when `a[i] == 0` should force `i == na`, allowing the return value to match the full-string specification.

2026-06-05 08:xx symexec repair 1

Phenomenon: `symexec` failed with `Cannot derive the precondition of Memory Read` at [annotated/verify_20260605_080838v_ex_hamming_distance.c:42](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_080838v_ex_hamming_distance.c:42), the `b[i]` read inside `if (a[i] != b[i])`.

Location: false branch after `if (a[i] == 0) break;`, where the VC needs the current index to be valid for the second string as well.

Repair action: make the equal-length relation available in the invariant as concrete arithmetic facts, not only through `ex_hamming_distance_pre(la, lb)`. I added `na == nb` and `i <= nb` to the loop invariant.

Key annotation delta:
```c
na == nb &&
i <= nb &&
```

Why this change: the branch-local fact `a[i] != 0` can help exclude the terminator case on `a`, but the second memory read still needs an explicit bound for `b`. Keeping the equal logical lengths in arithmetic form reduces dependence on unfolding `ex_hamming_distance_pre` during symbolic execution.
