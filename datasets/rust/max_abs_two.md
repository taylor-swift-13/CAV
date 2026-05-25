# Max Abs Two

## 问题描述

实现一个函数，返回 `a` 和 `b` 中绝对值较大的那个绝对值。

约定：

- 输入和结果都在 32 位有符号整数范围内。
- 如果两个绝对值相等，返回该绝对值。

## 参考实现

```rust
pub fn max_abs_two(mut a: i32, mut b: i32) -> i32 {
    if a < 0 { a = -a; }
    if b < 0 { b = -b; }
    if a > b { a } else { b }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
