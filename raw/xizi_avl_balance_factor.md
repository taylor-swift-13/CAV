# Xizi Avl Balance Factor

## 问题描述

实现一个函数，计算 AVL 结点的平衡因子。

这道题整理自 `kernel/thread/avl_tree.c` 中的 `AvlTreeGetNodeBalanceFactor`。为了避免递归和函数调用，直接输入左右子树高度。

约定：

- `left_height >= 0`
- `right_height >= 0`
- 返回 `left_height - right_height`

## 正确代码

```c
int xizi_avl_balance_factor(int left_height, int right_height) {
    return left_height - right_height;
}
```

## 说明

这道题适合验证 AVL 平衡因子的基本定义。
