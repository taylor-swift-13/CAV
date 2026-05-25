# Array Product Small

## 问题描述

实现一个函数，返回长度为 `n` 的整数数组所有元素乘积。

约定：

- `n >= 0`。
- 空数组乘积返回 `1`。
- 结果保证在 32 位有符号整数范围内。

## 参考实现

```rust
pub fn array_product_small(n: i32, a: &[i32]) -> i32 {
    let mut product = 1;
    let mut i = 0;
    while i < n { product *= a[i as usize]; i += 1; }
    product
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
