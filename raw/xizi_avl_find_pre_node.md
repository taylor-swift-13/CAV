# Xizi Avl Find Pre Node

## 问题描述

实现一个函数，寻找 AVL/BST 结点的前驱候选结点。

这道题整理自 `kernel/thread/avl_tree.c` 中的 `AvlTreeFindPreNode`。树指针用数组下标表示，`-1` 表示空指针。

约定：

- `node` 是有效结点下标
- `left[i]` 和 `right[i]` 分别表示左右孩子
- 若 `node` 没有左孩子，返回 `node`
- 若左孩子没有右孩子，返回左孩子
- 否则返回左子树中最右侧的结点

## 正确代码

```c
int xizi_avl_find_pre_node(int node, int *left, int *right) {
    int pre;

    if (left[node] != -1) {
        if (right[left[node]] != -1) {
            pre = right[left[node]];
            while (right[pre] != -1) {
                pre = right[pre];
            }
        } else {
            pre = left[node];
        }
    } else {
        pre = node;
    }

    return pre;
}
```

## 说明

这道题适合验证二叉搜索树中“左子树最大结点”的查找。
