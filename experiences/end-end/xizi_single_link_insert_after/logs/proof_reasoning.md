# Proof Reasoning

Generated obligation:

- one return witness proving that `linklist_node->node_next == first` plus `xizi_sll(first,l)` folds into `xizi_sll(linklist_node, cons(0,l))`.

Manual proof:

```coq
pre_process.
assert (Hnode : linklist_node_pre <> NULL) by tauto.
sep_apply (xizi_sll_cons linklist_node_pre 0 first l Hnode).
entailer!.
```

The strategy modules are still compiled because `xizi_single_link_def.h` includes `xizi_single_link.strategies`, but the function proof itself only needs `xizi_sll_cons`.
