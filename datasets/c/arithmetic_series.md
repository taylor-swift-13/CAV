# Arithmetic Series

## 问题描述

实现一个函数，返回等差数列前 `n` 项之和，首项为 `a`，公差为 `d`。

约定：

- `n >= 0`。
- `n == 0` 时返回 `0`。
- 结果保证在 32 位有符号整数范围内。

## 参考实现

```c
int arithmetic_series(int a, int d, int n) {
    int i = 0;
    int cur = a;
    int sum = 0;
    while (i < n) {
        sum += cur;
        cur += d;
        i++;
    }
    return sum;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
