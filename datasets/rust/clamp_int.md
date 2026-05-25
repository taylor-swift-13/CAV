# Clamp Int

## 问题描述

实现一个函数，把整数 `x` 限制在闭区间 `[lo, hi]` 内并返回结果。

约定：

- `lo <= hi`。
- 如果 `x < lo` 返回 `lo`。
- 如果 `x > hi` 返回 `hi`。
- 否则返回 `x`。

## 参考实现

```rust
pub fn clamp_int(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo { return lo; }
    if x > hi { return hi; }
    x
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
