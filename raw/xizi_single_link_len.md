# Xizi Single Link Len

## 问题描述

实现一个函数，计算带头结点单链表的长度。

这道题整理自 `kernel/thread/single_link.c` 中的 `SingleLinkListGetLen`。为了便于验证，链表指针用数组下标表示，`-1` 表示空指针。

约定：

- `head` 是头结点下标，不计入长度
- `next[i]` 表示结点 `i` 的后继下标
- `-1` 表示链表结束
- 链表无环
- 返回数据结点数量

## 正确代码

```c
int xizi_single_link_len(int head, int *next) {
    int length = 0;
    int node = next[head];

    while (node != -1) {
        node = next[node];
        length++;
    }

    return length;
}
```

## 说明

这道题适合验证单链表遍历和计数。
