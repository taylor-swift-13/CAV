# Xizi Double Link Get Head

## 问题描述

实现一个函数，返回双向循环链表的第一个数据结点。

这道题整理自 `kernel/thread/double_link.c` 中的 `DoubleLinkListGetHead`。链表指针用数组下标表示，`-1` 表示没有数据结点。

约定：

- `head` 是头结点下标
- 若 `next[head] == head`，链表为空，返回 `-1`
- 否则返回 `next[head]`

## 正确代码

```c
int xizi_double_link_get_head(int head, int *next) {
    if (next[head] == head) {
        return -1;
    }

    return next[head];
}
```

## 说明

这道题适合验证哨兵头结点结构下的首结点获取。
