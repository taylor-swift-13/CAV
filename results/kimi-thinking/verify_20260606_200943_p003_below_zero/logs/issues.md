# Issues Log — p003_below_zero

No blocking issues. All generated verification conditions were discharged:

- `safety_wit_3` — proved by extracting array length with `prop_apply IntArray.full_Zlength`, reducing the spatial goal with `entailer!`, and relating `num + Znth i l 0` to the bounded prefix sum `sum (sublist 0 (i + 1) l)` via `sublist_split` / `sublist_single`.
- `entail_wit_1` — trivial initialization obligation solved immediately by `pre_process`.
- `entail_wit_2` — spatial cancellation of the unchanged `IntArray.full` array, then the same `sublist_split` / `sublist_single` rewrite chain to show the updated `num` equals the next prefix sum.
- `entail_wit_3` — loop-invariant preservation for the `num >= 0` branch. After cancelling the array resource, a case analysis on `k <? i` combines the inductive prefix hypothesis with the current `num >= 0` fact.
- `return_wit_1` — normal loop exit. The left disjunct (`__return = 0` and all prefix sums non-negative) follows from `i = operations_size_pre` and the invariant.

All Coq sources (`goal.v`, `proof_auto.v`, `proof_manual.v`, `goal_check.v`) compile without axioms (`Admitted`/`Axiom`) remaining.
