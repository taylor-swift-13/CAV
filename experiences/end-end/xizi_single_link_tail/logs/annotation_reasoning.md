# Annotation Reasoning

Target: `SingleLinkListGetTailNode`.

The original loop walks along `node_next` until the current node's next pointer is null:

```c
while (linklist->node_next) {
    linklist = linklist->node_next;
}
return linklist;
```

The contract models the whole headed chain from the original `linklist` as `xizi_sll(linklist,l)`. The postcondition returns a real tail node and preserves the chain as a prefix segment plus the tail field:

```c
exists l1 d,
  l == app(l1, cons(d, nil)) &&
  __return != 0 &&
  xizi_sllseg(linklist@pre, __return, l1) *
  (__return -> node_next == 0)
```

The loop invariant uses the same prefix/current/suffix shape as append:

```c
exists l1 d l2 next,
  l == app(l1, cons(d, l2)) &&
  linklist != 0 &&
  linklist -> node_next == next &&
  xizi_sllseg(linklist@pre, linklist, l1) *
  xizi_sll(next, l2)
```

No array or index model is used.
