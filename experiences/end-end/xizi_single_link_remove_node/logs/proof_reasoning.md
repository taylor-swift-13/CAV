# Proof Reasoning

Generated obligations:

- `safety_wit_1`: integer zero-literal range, closed by `pre_process`.
- `safety_wit_2`: false branch after the assert, closed by pure contradiction from `node_node_next = 0`, `node_node_next = linklist_node_pre`, and `linklist_node_pre <> 0`.
- `partial_solve_wit_1`: after `node->node_next` is known to be the target, expose `linklist_node->node_next == target_next` for the RHS read.
- `entail_wit_1`: initialize the invariant by unfolding `xizi_sll_to_target(linklist, linklist_node, l_before)` under `linklist != linklist_node`.
- `entail_wit_2`: advance one node by unfolding `xizi_sll_to_target(next_2, linklist_node, l2_2)`, then append the current field to the visited prefix with `xizi_sllseg_len1` and `xizi_sllseg_sllseg`.
- `entail_wit_3_1`: exclude the `next == 0` loop-exit case with `xizi_sll_to_target_zero_nonzero`.
- `entail_wit_3_2`: use `xizi_sll_to_target_same` to derive the remaining suffix is nil when `next == linklist_node`.
- `return_wit_1`: fold `node -> node_next == target_next * xizi_sll(target_next, l_after)` with `xizi_sll_cons`, then fold the visited prefix with `xizi_sllseg_sll`.

New XiZi proof support:

- `xizi_sll_to_target`: first-occurrence path predicate for removal-by-target.
- `xizi_sll_to_target_not_same`: left-unfold when current pointer is not the target.
- `xizi_sll_to_target_same`: same endpoint forces empty remaining target path.
- `xizi_sll_to_target_zero_nonzero`: null cannot be a path to a non-null target.
- strategies `309` and `310` mirror the new predicate's unfold/fold behavior.

The final audit re-ran `symexec`, restored checked proof files, compiled deps/goal/proofs/goal_check, and found no proof obligation markers.
