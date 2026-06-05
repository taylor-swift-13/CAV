# Array Count Negative

## 问题描述

实现一个函数，统计长度为 `n` 的整数数组中负数元素个数。

约定：

- `n >= 0`。
- 数组长度至少为 `n`。
- 只统计严格小于零的元素。

## 参考实现

```c
int array_count_negative(int n, int *a) {
    int count = 0;
    for (int i = 0; i < n; i++) if (a[i] < 0) count++;
    return count;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
