2026-06-05

Phenomenon: `symexec` failed on `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_004036v_array_none_zero.c` at the `for` loop (`array_none_zero`, line 22) with `Error: Lack of assertions in some paths for the loop!`.

Location: annotated C file `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_004036v_array_none_zero.c`, loop statement `for (i = 0; i < n; i++)`.

Repair action: add a loop invariant that matches the real control point of the `for`: after initialization and before the loop guard. The invariant will keep `0 <= i <= n` and the semantic summary of the processed prefix, namely `forall k, 0 <= k < i -> l[k] != 0`.

Key code/log fragment:

```text
fatal error: Error: Lack of assertions in some paths for the loop!
```

Planned annotation shape:

```c
/*@ Inv
      0 <= i && i <= n &&
      (forall (k: Z), (0 <= k && k < i) => l[k] != 0)
*/
```

Why this change: the function is a read-only single scan. At the loop head, `i` is the next element to inspect, so the strongest useful summary is that every earlier position has already been checked and found nonzero. This is sufficient for initialization (`i == 0`), preservation (if `a[i] != 0`, extend the prefix by one), the early return (`a[i] == 0` witnesses the existential), and the normal exit (`i == n` implies all indices in range are nonzero).

2026-06-05

Phenomenon: after adding the prefix invariant, `symexec` advanced to the loop body but failed at the read `a[i]` with `Cannot derive the precondition of Memory Read.` at `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_004036v_array_none_zero.c:27:8`.

Location: annotated C file `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_004036v_array_none_zero.c`, loop-body array access `a[i]`.

Repair action: strengthen the loop invariant to explicitly carry the unchanged array ownership predicate `IntArray::full(a, n, l)` along with the pure prefix property.

Key code/log fragment:

```text
fatal error: Cannot derive the precondition of Memory Read.
```

Planned annotation delta:

```c
/*@ Inv
      0 <= i && i <= n &&
      (forall (k: Z), (0 <= k && k < i) => l[k] != 0) &&
      IntArray::full(a, n, l)
*/
```

Why this change: loop invariants in this front end must preserve both the pure summary and the heap/resource shape needed by later commands. The read `a[i]` needs the full-array predicate at the loop head; keeping only the prefix fact leaves no memory ownership fact to consume for the read.
