# Arithmetic Series

## 问题描述

实现一个函数，返回等差数列前 `n` 项之和，首项为 `a`，公差为 `d`。

约定：

- `n >= 0`。
- `n == 0` 时返回 `0`。
- 结果保证在 32 位有符号整数范围内。

## 参考实现

```rust
pub fn arithmetic_series(a: i32, d: i32, n: i32) -> i32 {
    let mut i = 0;
    let mut cur = a;
    let mut sum = 0;
    while i < n {
        sum += cur;
        cur += d;
        i += 1;
    }
    sum
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
