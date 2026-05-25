# Array Count Negative

## 问题描述

实现一个函数，统计长度为 `n` 的整数数组中负数元素个数。

约定：

- `n >= 0`。
- 数组长度至少为 `n`。
- 只统计严格小于零的元素。

## 参考实现

```rust
pub fn array_count_negative(n: i32, a: &[i32]) -> i32 {
    let mut count = 0;
    let mut i = 0;
    while i < n { if a[i as usize] < 0 { count += 1; } i += 1; }
    count
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
