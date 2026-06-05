## 2026-06-03 19:07:16 +0800

Phenomenon: `annotated/verify_20260603_190108v_xizi_id_first_nonfull_byte.c` had no loop annotation for the `for (i = 0; i < n; ++i)` scan, so verify lacked the prefix fact needed to justify both the early return branch and the `-1` return after loop exit.

Location: [annotated/verify_20260603_190108v_xizi_id_first_nonfull_byte.c](/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_190108v_xizi_id_first_nonfull_byte.c:18), loop over `i` in `xizi_id_first_nonfull_byte`.

Repair action: Added a single loop invariant that records `0 <= i <= n`, preserves `IntArray::full(id_map, n, l)`, and states that every already processed index `j < i` has low byte `255`.

Key annotation snippet:

```c
/*@ Inv
      0 <= i && i <= n &&
      (forall (j: Z), (0 <= j && j < i) => ((l[j] & 255) == 255)) &&
      IntArray::full(id_map, n, l)
*/
```

Why this change: This loop is a left-to-right search. The natural inductive summary is a prefix property over processed elements. At early return, the invariant supplies the postcondition clause for all earlier indices. At loop exit, `i == n` together with the same prefix property yields the `__return == -1` clause without changing the original contract or executable C body.

## 2026-06-03 19:07:16 +0800

Phenomenon: The first fresh `symexec` run failed with `fatal error: Expected loop after loop invariant.` for the invariant near line 28 of the annotated file.

Location: [annotated/verify_20260603_190108v_xizi_id_first_nonfull_byte.c](/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_190108v_xizi_id_first_nonfull_byte.c:18), parse error at the loop annotation control point.

Repair action: Moved the same `Inv` block from the top of the loop body to the required position immediately before the `for` statement.

Key error/log snippet:

```text
fatal error: Expected loop after loop invariant.
```

Why this change: Per the verify frontend, a loop invariant annotates the loop statement itself, not the first statement inside the loop body. Keeping the invariant semantics identical while changing its placement aligns the annotation with the parser’s expected control point.

## 2026-06-03 19:07:16 +0800

Phenomenon: Compiling `return_wit_1` in the regenerated proof showed that the VC still distinguished current `n` / `id_map` from `n_pre` / `id_map_pre`, leaving the preserved `IntArray.full` resource stuck on current parameters instead of the pre-state ones.

Location:
- [annotated/verify_20260603_190108v_xizi_id_first_nonfull_byte.c](/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_190108v_xizi_id_first_nonfull_byte.c:18), loop invariant
- [xizi_id_first_nonfull_byte_proof_manual.v](/home/yangfp/CAV/OS/CAV/output/verify_20260603_190108v_xizi_id_first_nonfull_byte/coq/generated/xizi_id_first_nonfull_byte_proof_manual.v:40), `proof_of_xizi_id_first_nonfull_byte_return_wit_1`

Repair action: Strengthened the loop invariant with explicit unchanged-parameter facts `n == n@pre` and `id_map == id_map@pre`.

Key proof/VC symptom:

```text
Unable to unify ... Z.land (Znth ?j l 0) 255 = 255
with IntArray.full id_map_pre n_pre l
```

Why this change: The proof guide’s “current vs pre parameter pollution” case applies here. Since `n` and `id_map` are never modified, their identity belongs in the annotation layer. Carrying those equalities in the invariant should let the regenerated return witnesses preserve `IntArray.full` directly on the pre-state parameters instead of forcing a brittle proof-side reconstruction.
