# Fibonacci

## 问题描述

实现一个函数，输入整数 `n`，返回第 `n` 个 Fibonacci 数。

约定：

- `n >= 0`
- `fib(0) = 0`
- `fib(1) = 1`
- 对 `n >= 2`，`fib(n) = fib(n - 1) + fib(n - 2)`

## 参考实现

```rust
pub fn fibonacci(mut n: i32) -> i32 {
    let mut i: i32;
    let mut a: i32 = 0;
    let mut b: i32 = 1;
    let mut c: i32;

    if n == 0 {
        return 0;
    }

    i = 2;
    while i <= n {
        c = a + b;
        a = b;
        b = c;
        i += 1;
    }

    return b;
}
```

## 说明

这是最简单的动态规划题之一，适合验证“两状态滚动数组”的循环不变量。
