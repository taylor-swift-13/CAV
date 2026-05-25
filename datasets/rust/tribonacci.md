# Tribonacci

## 问题描述

实现一个函数，输入整数 `n`，返回第 `n` 个 Tribonacci 数。

约定：

- `n >= 0`
- `tri(0) = 0`
- `tri(1) = 1`
- `tri(2) = 1`
- 对 `n >= 3`，`tri(n) = tri(n - 1) + tri(n - 2) + tri(n - 3)`

## 参考实现

```rust
pub fn tribonacci(mut n: i32) -> i32 {
    let mut i: i32;
    let mut a: i32 = 0;
    let mut b: i32 = 1;
    let mut c: i32 = 1;
    let mut d: i32;

    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }

    i = 3;
    while i <= n {
        d = a + b + c;
        a = b;
        b = c;
        c = d;
        i += 1;
    }

    return c;
}
```

## 说明

这是 Fibonacci 的三状态版本，适合验证“固定数量状态量滚动更新”。
