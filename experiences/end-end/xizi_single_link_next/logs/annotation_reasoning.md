# Annotation Reasoning

Target: `SingleLinkListGetNextNode`.

The original function reads and returns one node's direct successor:

```c
return linklist_node->node_next;
```

The contract is the generic XiZi read-only accessor shape:

```c
/*@ With next l
    Require
      linklist_node != 0 &&
      (linklist_node -> node_next == next) *
      xizi_sll(next, l)
    Ensure
      __return == next &&
      (linklist_node -> node_next == next) *
      xizi_sll(next, l)
*/
```

It preserves both the field cell and the suffix list predicate. No array or index model is used.
