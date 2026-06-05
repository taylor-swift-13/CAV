# Array Count Odd

## 问题描述

实现一个函数，返回长度为 `n` 的整数数组中奇数元素的个数。

约定：

- `n >= 0`。
- 数组长度至少为 `n`。
- 负奇数也应被计入。

## 参考实现

```c
int array_count_odd(int n, int *a) {
    int i = 0;
    int count = 0;
    while (i < n) {
        if (a[i] % 2 != 0) count++;
        i++;
    }
    return count;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
