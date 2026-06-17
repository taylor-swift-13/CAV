# Annotation Reasoning

Target: XiZi `AppendSingleLinkList`.

The staged C keeps the original XiZi control flow:

```c
node = linklist;
while (node->node_next) node = node->node_next;
node->node_next = linklist_node;
linklist_node->node_next = (void *)0;
```

No array/index representation is used.

The contract uses `xizi_sll(linklist, l)` as a shape predicate for the whole chain rooted at the head node. This is intentional for `append`, because the original implementation starts traversal from the head node itself and appends after the last reachable node.

The loop invariant mirrors QCP's `sll` append pattern:

```c
exists l1a d l1b next,
  l == app(l1a, cons(d, l1b)) &&
  linklist == linklist@pre &&
  linklist_node == linklist_node@pre &&
  node != 0 &&
  node -> node_next == next &&
  xizi_sllseg(linklist, node, l1a) *
  xizi_sll(next, l1b) &&
  linklist_node -> node_next == old_next
```

The two `@pre` equalities are necessary. Without them, the generated return witness forgets that the segment root and appended node are the original function parameters.
