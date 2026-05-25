# Fibonacci Mod

## 问题描述

实现一个函数，输入非负整数 `n` 和正整数 `mod`，返回第 `n` 个 Fibonacci 数对 `mod` 取模后的结果。

约定：

- `n >= 0`
- `mod > 0`
- `fib(0) = 0`
- `fib(1) = 1`
- 对 `n >= 2`，`fib(n) = fib(n - 1) + fib(n - 2)`
- 每一步都对 `mod` 取模

## 参考实现

```rust
pub fn fibonacci_mod(mut n: i32, r#mod: i32) -> i32 {
    let mut i: i32;
    let mut a: i32 = 0;
    let mut b: i32 = 1 % r#mod;
    let mut c: i32;

    if n == 0 {
        return 0;
    }

    i = 2;
    while i <= n {
        c = (a + b) % r#mod;
        a = b;
        b = c;
        i += 1;
    }

    return b;
}
```

## 说明

这是 Fibonacci 的取模版本，适合验证“滚动状态 + 模运算保持范围”。
