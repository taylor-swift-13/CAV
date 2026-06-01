# Xizi Single Link Remove Node

## 问题描述

实现一个函数，从带头结点单链表中删除目标结点 `target`。

这道题整理自 `kernel/thread/single_link.c` 中的 `SingleLinkListRmNode`。链表指针用数组下标表示，`-1` 表示空指针。

约定：

- `head` 是头结点下标
- 链表无环
- 若 `target` 在链表中，则把它从链表中摘除并返回 `1`
- 若 `target` 不在链表中，则链表不变并返回 `0`

## 正确代码

```c
int xizi_single_link_remove_node(int head, int target, int *next) {
    int node = head;

    while (next[node] != -1 && next[node] != target) {
        node = next[node];
    }

    if (next[node] != -1) {
        next[node] = next[next[node]];
        return 1;
    }

    return 0;
}
```

## 说明

这道题适合验证“寻找前驱结点后摘链”的单链表删除模式。
