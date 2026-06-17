# Annotation Reasoning

This workspace verifies the target-absent/no-op branch of XiZi `SingleLinkListRmNode`.

The raw function has two behaviors:

- if `linklist_node` is reachable through `node_next`, unlink it;
- if it is not reachable, traverse to the tail and leave the list unchanged.

The present case is verified separately in `verify_20260615_hil_xizi_single_link_remove_node`.
This workspace closes the absent case with `xizi_sll_not_target(linklist, linklist_node, l)`.

Loop invariant:

- `xizi_sllseg(linklist,node,l1)` owns the visited prefix;
- `node->node_next == next` owns the current field tested by the loop;
- `xizi_sll_not_target(next, linklist_node,l2)` owns the remaining suffix and records that target is absent;
- `l == app(l1, cons(d,l2))` keeps the current node token needed to rebuild the list.

At exit, `next == linklist_node` is impossible by `xizi_sll_not_target_same_nonzero`; the remaining valid exit is `next == 0`, so the `if` body is skipped and the list is rebuilt unchanged.
