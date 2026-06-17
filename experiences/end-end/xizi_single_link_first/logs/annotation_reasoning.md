# Annotation Reasoning

Target: `SingleLinkListGetFirstNode`.

The original function reads and returns the headed list's first data node:

```c
return linklist->node_next;
```

The contract keeps the head field as an owned XiZi pointer cell and preserves the data chain:

```c
/*@ With first l
    Require
      linklist != 0 &&
      (linklist -> node_next == first) *
      xizi_sll(first, l)
    Ensure
      __return == first &&
      (linklist -> node_next == first) *
      xizi_sll(first, l)
*/
```

This is a read-only accessor: it does not need a loop invariant, and it does not need to unfold `xizi_sll`. No array or index model is used.
