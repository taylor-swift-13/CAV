# Xizi Single Link Insert After

## 问题描述

实现一个函数，把结点 `node` 插入到单链表结点 `pos` 之后。

这道题整理自 `kernel/thread/single_link.c` 中的 `SingleLinkListNodeInsert`。链表指针用数组下标表示，`-1` 表示空指针。

约定：

- `pos` 是链表中的有效结点
- `node` 是待插入结点，且当前不在链表中
- 函数只修改 `next[node]` 和 `next[pos]`
- 插入后，`node` 成为 `pos` 的直接后继

## 正确代码

```c
void xizi_single_link_insert_after(int pos, int node, int *next) {
    next[node] = next[pos];
    next[pos] = node;
}
```

## 说明

这道题适合验证单链表插入时两次指针赋值的顺序。
