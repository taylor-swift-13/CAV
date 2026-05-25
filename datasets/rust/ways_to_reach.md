# Ways To Reach

## 问题描述

实现一个函数，输入非负整数 `n`，每次可以走 `1` 步或 `2` 步，返回到达第 `n` 级台阶的方法数。

约定：

- `n >= 0`
- `ways(0) = 1`
- `ways(1) = 1`
- 对 `n >= 2`，`ways(n) = ways(n - 1) + ways(n - 2)`

## 参考实现

```rust
pub fn ways_to_reach(mut n: i32) -> i32 {
    let mut i: i32;
    let mut a: i32 = 1;
    let mut b: i32 = 1;
    let mut c: i32;

    if n == 0 {
        return 1;
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

这是最简单的台阶 DP，和 Fibonacci 类似但初值不同。
