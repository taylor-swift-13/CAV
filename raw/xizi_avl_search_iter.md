# Xizi Avl Search Iter

## 问题描述

实现一个函数，在二叉搜索树中查找目标值。

这道题整理自 `kernel/thread/avl_tree.c` 中的 `AvlNodeSearchNode`。原实现是递归；这里改写为迭代单函数，避免函数调用。

约定：

- `root` 是根结点下标，`-1` 表示空树
- `data[i]` 是结点 `i` 的键值
- `left[i]` 和 `right[i]` 分别表示左右孩子
- 二叉搜索树满足左小右大
- 若找到 `target`，返回结点下标
- 否则返回 `-1`

## 正确代码

```c
int xizi_avl_search_iter(int root, int target, int *data, int *left, int *right) {
    int node = root;

    while (node != -1) {
        if (target == data[node]) {
            return node;
        } else if (data[node] < target) {
            node = right[node];
        } else {
            node = left[node];
        }
    }

    return -1;
}
```

## 说明

这道题适合验证二叉搜索树的分支查找路径。
