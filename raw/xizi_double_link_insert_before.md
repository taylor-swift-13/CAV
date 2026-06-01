# Xizi Double Link Insert Before

## 问题描述

实现一个函数，把结点 `node` 插入到双向循环链表结点 `pos` 之前。

这道题整理自 `kernel/thread/double_link.c` 中的 `DoubleLinkListInsertNodeBefore`。链表指针用数组下标表示。

约定：

- `pos` 是链表中的有效结点
- `node` 是待插入结点，且当前不在链表中
- 链表结构合法
- 函数维护 `next` 和 `prev` 的双向一致性

## 正确代码

```c
void xizi_double_link_insert_before(int pos, int node, int *next, int *prev) {
    int old_prev = prev[pos];

    next[old_prev] = node;
    prev[node] = old_prev;
    prev[pos] = node;
    next[node] = pos;
}
```

## 说明

这道题适合验证双向链表在目标结点前插入时的四次赋值。
