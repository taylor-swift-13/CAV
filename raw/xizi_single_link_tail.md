# Xizi Single Link Tail

## 问题描述

实现一个函数，返回带头结点单链表的尾结点下标。

这道题整理自 `kernel/thread/single_link.c` 中的 `SingleLinkListGetTailNode`。链表指针用数组下标表示，`-1` 表示空指针。

约定：

- `head` 是头结点下标
- 若链表为空，尾结点就是 `head`
- 链表无环
- 返回最后一个满足 `next[node] == -1` 的结点下标

## 正确代码

```c
int xizi_single_link_tail(int head, int *next) {
    int node = head;

    while (next[node] != -1) {
        node = next[node];
    }

    return node;
}
```

## 说明

这道题适合验证沿单链表走到末尾的循环不变式。
