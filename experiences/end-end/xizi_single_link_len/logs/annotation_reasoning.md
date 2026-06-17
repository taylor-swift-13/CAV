# Annotation Reasoning

Target: `SingleLinkListGetLen`.

The original function is a read-only traversal of a XiZi headed singly linked list:

```c
unsigned int length = 0;
const SysSingleLinklistType *tmp_list = linklist->node_next;
while (tmp_list != NONE) {
    tmp_list = tmp_list->node_next;
    length++;
}
return length;
```

The staged program keeps the `const SysSingleLinklistType *` source shape because QCP accepts it. The executable control flow is unchanged except spelling `NONE` as `(void *)0` in the closed input.

The contract uses XiZi's own node definition and predicates:

- `linklist -> node_next == first` keeps the head cell explicit.
- `xizi_sll(first, l)` models the data chain after the head node.
- `Zlength(l) <= UINT_MAX` is required because the return value and counter are `unsigned int`.
- The postcondition returns `Zlength(l)` and preserves the head cell and data chain.

The loop invariant follows QCP's linked-list length example but uses XiZi predicates:

```c
exists l1 l2,
  l == app(l1, l2) &&
  length == Zlength(l1) &&
  linklist == linklist@pre &&
  linklist -> node_next == first &&
  xizi_sllseg(first, tmp_list, l1) *
  xizi_sll(tmp_list, l2)
```

This states that `l1` is the already traversed prefix, `tmp_list` is the current pointer, and `l2` is the remaining suffix. No array or index model is used.
