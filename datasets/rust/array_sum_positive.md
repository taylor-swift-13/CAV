# Array Sum Positive

## 问题描述

实现一个函数，返回长度为 `n` 的整数数组中所有正数之和。

约定：

- `n >= 0`。
- 零和负数不计入。
- 结果保证在 32 位有符号整数范围内。

## 参考实现

```rust
pub fn array_sum_positive(n: i32, a: &[i32]) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n { if a[i as usize] > 0 { sum += a[i as usize]; } i += 1; }
    sum
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
