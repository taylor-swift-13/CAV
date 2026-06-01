# Xizi Double Link Get Next

## 问题描述

实现一个函数，返回双向循环链表中某结点的下一个数据结点。

这道题整理自 `kernel/thread/double_link.c` 中的 `DoubleLinkListGetNext`。链表指针用数组下标表示，`-1` 表示已经到达链表尾部。

约定：

- `head` 是头结点下标
- `node` 是链表中的数据结点
- 若 `next[node] == head`，返回 `-1`
- 否则返回 `next[node]`

## 正确代码

```c
int xizi_double_link_get_next(int head, int node, int *next) {
    if (next[node] == head) {
        return -1;
    }

    return next[node];
}
```

## 说明

这道题适合验证双向循环链表遍历时对头结点的终止判断。
