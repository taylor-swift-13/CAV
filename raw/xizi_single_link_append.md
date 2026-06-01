# Xizi Single Link Append

## 问题描述

实现一个函数，把结点 `node` 追加到带头结点单链表尾部。

这道题整理自 `kernel/thread/single_link.c` 中的 `AppendSingleLinkList`。链表指针用数组下标表示，`-1` 表示空指针。

约定：

- `head` 是头结点下标
- 链表无环
- `node` 是待追加结点，且当前不在链表中
- 追加后 `node` 的后继为 `-1`
- 返回原尾结点下标

## 正确代码

```c
int xizi_single_link_append(int head, int node, int *next) {
    int tail = head;

    while (next[tail] != -1) {
        tail = next[tail];
    }

    next[tail] = node;
    next[node] = -1;

    return tail;
}
```

## 说明

这道题适合验证先找尾结点再追加的单链表操作。
