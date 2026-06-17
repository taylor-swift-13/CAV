# Annotation Reasoning

Target: XiZi `InitSingleLinkList`.

Original code:

```c
void InitSingleLinkList(SysSingleLinklistType *linklist)
{
    linklist->node_next = NONE;
}
```

Staged code keeps the XiZi intrusive node definition and rewrites `NONE` as `(void *)0` because the QCP frontend does not handle the original macro syntax in the local header.

The contract only requires ownership of the head node's `node_next` cell:

```c
Require linklist != 0 && linklist -> node_next == first
Ensure  linklist -> node_next == 0 && xizi_sll(0, nil)
```

This is intentionally shape-only. The XiZi single-link node has no payload field; `xizi_sll(0, nil)` records that the initialized successor list is empty.

No array/index model is used.
