# Array Product Small

## 问题描述

实现一个函数，返回长度为 `n` 的整数数组所有元素乘积。

约定：

- `n >= 0`。
- 空数组乘积返回 `1`。
- 结果保证在 32 位有符号整数范围内。

## 参考实现

```java
class ArrayProductSmall {
    public static int array_product_small(int n, int[] a) {
        int product = 1;
        for (int i = 0; i < n; i++) product *= a[i];
        return product;
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
