# Array Index Of Min

## 问题描述

实现一个函数，返回长度为 `n` 的非空整数数组中最小值第一次出现的位置。

约定：

- `n > 0`。
- 数组长度至少为 `n`。
- 如果最小值出现多次，返回最小下标。

## 参考实现

```c
int array_index_of_min(int n, int *a) {
    int idx = 0;
    int i = 1;
    while (i < n) {
        if (a[i] < a[idx]) idx = i;
        i++;
    }
    return idx;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
