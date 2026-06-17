# Annotation Reasoning

## Closed XiZi Pointer Model

The target is `IsSingleLinkListEmpty` from XiZi `kernel/thread/single_link.c`, staged as `xizi_single_link_empty`.

The program is kept as a closed XiZi pointer program:

```c
typedef struct SingleLinklistNode
{
    struct SingleLinklistNode *node_next;
} SysSingleLinklistType;
```

The contract uses the concrete head-node field cell plus a tail linked-list predicate:

```c
Require
  linklist != 0 &&
  linklist -> node_next == first &&
  xizi_sll(first, l)
Ensure
  (first == 0 => __return == 1) &&
  (first != 0 => __return == 0) &&
  linklist -> node_next == first &&
  xizi_sll(first, l)
```

The verified heap resource is the XiZi `SingleLinklistNode.node_next` field.

## QCP Header Shape

QCP symexec does not fully preprocess case-local headers. Earlier attempts with include guards and `#define NONE (0)` failed before symbolic execution on `#` characters. The staged QCP header therefore contains only the XiZi struct/typedef and Coq declarations.

The executable uses `(void *)0` in place of XiZi `NONE`, matching `xs_base.h` where `NONE` is defined as `0`:

```c
return linklist->node_next == (void *)0;
```

## Strategy Decision

The local `xizi_sll` predicate is imported from `xizi_single_link_lib.v`. A temporary `xizi_single_link.strategies` include made symexec generate imports for `xizi_single_link_strategy_goal` and `xizi_single_link_strategy_proof`; those modules were not present, so `goal.v` compilation failed.

For this straight-line empty check, the contract keeps the head field cell explicit and does not need to unfold/fold `xizi_sll`. The strategy include was removed for this case. Looping list functions such as append, len, tail, and remove should either add explicit assertions that avoid strategy use or provide proper XiZi strategy goal/proof modules.
