# Digit Product

## 问题描述

实现一个函数，返回非负整数 `n` 的十进制各位数字乘积。

约定：

- `n >= 0`。
- `n == 0` 时返回 `0`。
- 结果保证在 32 位有符号整数范围内。

## 参考实现

```c
int digit_product(int n) {
    if (n == 0) return 0;
    int product = 1;
    while (n > 0) {
        product *= n % 10;
        n /= 10;
    }
    return product;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
