# Xizi Double Link Remove Node

## 问题描述

实现一个函数，从双向循环链表中摘除结点 `node`，并把该结点重置为自环。

这道题整理自 `kernel/thread/double_link.c` 中的 `DoubleLinkListRmNode`。链表指针用数组下标表示。

约定：

- `node` 是链表中的有效非头结点
- 链表结构合法
- 删除后，原前驱和原后继互相连接
- 删除后，`node` 的 `next` 和 `prev` 都指向自身

## 正确代码

```c
void xizi_double_link_remove_node(int node, int *next, int *prev) {
    int old_next = next[node];
    int old_prev = prev[node];

    prev[old_next] = old_prev;
    next[old_prev] = old_next;
    next[node] = node;
    prev[node] = node;
}
```

## 说明

这道题适合验证双向链表摘链和被摘结点复位。
