# Array Sum Nonnegative

## 问题描述

实现一个函数，返回长度为 `n` 的整数数组中所有非负数之和。

约定：

- `n >= 0`。
- 只累加大于等于零的元素。
- 结果保证在 32 位有符号整数范围内。

## 参考实现

```c
int array_sum_nonnegative(int n, int *a) {
    int sum = 0;
    for (int i = 0; i < n; i++) if (a[i] >= 0) sum += a[i];
    return sum;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
