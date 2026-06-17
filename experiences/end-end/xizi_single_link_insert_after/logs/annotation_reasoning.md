# Annotation Reasoning

Target: XiZi `SingleLinkListNodeInsert`.

Original behavior:

```c
linklist_node->node_next = linklist->node_next;
linklist->node_next = linklist_node;
```

The contract models a local splice after `linklist`:

```c
Require
  linklist != 0 &&
  linklist_node != 0 &&
  linklist -> node_next == first &&
  xizi_sll(first, l) &&
  linklist_node -> node_next == old_next
Ensure
  linklist -> node_next == linklist_node &&
  xizi_sll(linklist_node, cons(0, l))
```

`old_next` is only needed to own the inserted node's field before overwriting it. The postcondition states that the inserted node points to the old suffix. No array or index model is used.
