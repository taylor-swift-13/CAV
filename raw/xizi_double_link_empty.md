# Xizi Double Link Empty

## 问题描述

实现一个函数，判断带头结点的双向循环链表是否为空。

这道题整理自 `kernel/thread/double_link.c` 中的 `IsDoubleLinkListEmpty`。链表指针用数组下标表示。

约定：

- `head` 是头结点下标
- 空链表满足 `next[head] == head`
- 返回 `1` 表示为空，返回 `0` 表示非空

## 正确代码

```c
int xizi_double_link_empty(int head, int *next) {
    if (next[head] == head) {
        return 1;
    }

    return 0;
}
```

## 说明

这道题适合验证双向循环链表的哨兵头结点判空条件。
