# Xizi Double Link Len

## 问题描述

实现一个函数，计算带头结点双向循环链表的长度。

这道题整理自 `kernel/thread/double_link.c` 中的 `DoubleLinkListLenGet`。链表指针用数组下标表示。

约定：

- `head` 是头结点下标，不计入长度
- 非空链表从 `next[head]` 开始
- 遍历回到 `head` 时结束
- 链表结构合法

## 正确代码

```c
int xizi_double_link_len(int head, int *next) {
    int length = 0;
    int node = head;

    while (next[node] != head) {
        node = next[node];
        length++;
    }

    return length;
}
```

## 说明

这道题适合验证以哨兵头结点为终止条件的循环链表遍历。
