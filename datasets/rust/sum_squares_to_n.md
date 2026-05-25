# Sum Squares To N

## 问题描述

实现一个函数，返回 `1^2 + 2^2 + ... + n^2`。

约定：

- `n >= 0`。
- `n == 0` 时返回 `0`。
- 结果保证在 32 位有符号整数范围内。

## 参考实现

```rust
pub fn sum_squares_to_n(n: i32) -> i32 {
    let mut i = 1;
    let mut sum = 0;
    while i <= n {
        sum += i * i;
        i += 1;
    }
    sum
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
