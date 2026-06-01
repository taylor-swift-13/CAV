# Xizi Avl Left Rotate

## 问题描述

实现一个函数，对用数组下标表示的 AVL 子树做一次左旋。

这道题整理自 `kernel/thread/avl_tree.c` 中的 `AvlTreeSetLeftRotate`。这里用 `left`、`right` 和 `height` 数组建模结点字段，`-1` 表示空指针。

约定：

- `root` 是待旋转子树根
- `right[root]` 不是 `-1`
- `height[i]` 是结点 `i` 当前子树高度
- 函数更新必要的左右孩子指针和两个受影响结点的高度
- 返回旋转后的新根

## 正确代码

```c
int xizi_avl_left_rotate(int root, int *left, int *right, int *height) {
    int new_root = right[root];
    int moved = left[new_root];
    int lh;
    int rh;

    right[root] = moved;
    left[new_root] = root;

    lh = (left[root] == -1) ? 0 : height[left[root]];
    rh = (right[root] == -1) ? 0 : height[right[root]];
    height[root] = ((lh > rh) ? lh : rh) + 1;

    lh = (left[new_root] == -1) ? 0 : height[left[new_root]];
    rh = (right[new_root] == -1) ? 0 : height[right[new_root]];
    height[new_root] = ((lh > rh) ? lh : rh) + 1;

    return new_root;
}
```

## 说明

这道题适合验证 AVL 左旋的指针重连和局部高度更新。
