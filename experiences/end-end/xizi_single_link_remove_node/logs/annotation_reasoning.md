# Annotation Reasoning

Target: `SingleLinkListRmNode`.

The original function searches from the head node until `node->node_next` is either `NONE` or the target `linklist_node`, then unlinks the target by assigning the predecessor's `node_next`.

The staged program keeps the XiZi intrusive list representation:

```c
typedef struct SingleLinklistNode {
    struct SingleLinklistNode *node_next;
} SysSingleLinklistType;
```

No array, index, `next[]`, or sentinel-index model is used.

The verified contract covers the target-present case:

```c
xizi_sll_to_target(linklist, linklist_node, l_before) *
(linklist_node -> node_next == target_next) *
xizi_sll(target_next, l_after)
```

`xizi_sll_to_target(x, y, l)` is a XiZi pointer predicate for a path from `x` to `y` where every non-final node is not `y`. It matches the C loop condition `node->node_next != linklist_node` and avoids the unsound left-elimination of a general `xizi_sllseg(y, y, l)`.

The loop invariant splits the heap into:

- visited prefix: `xizi_sllseg(linklist, node, l1)`
- current field: `node -> node_next == next`
- remaining first-target path: `xizi_sll_to_target(next, linklist_node, l2)`
- detached target tail: `linklist_node -> node_next == target_next * xizi_sll(target_next, l_after)`

After the loop, `next == linklist_node` implies `l2 == nil`; the assignment changes `node->node_next` to `target_next`, and the proof folds the remaining chain back into `xizi_sll(linklist, app(l_before, l_after))`.
