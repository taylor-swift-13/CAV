# Climbing Stairs

## 问题描述

给定一个非负整数 `n`，表示爬到第 `n` 阶台阶。

每次你只能爬 `1` 阶或者 `2` 阶。请返回一共有多少种不同的方法可以爬到第 `n` 阶。

约定：
- `n = 0` 时返回 `1`，表示什么都不做也算一种方式。
- `n = 1` 时返回 `1`。
- 输入 `n` 为非负整数。

## 参考实现

```rust
pub fn climbStairs(n: i32) -> i32 {
    if n <= 1 { return 1; }
    let mut prev2: i32 = 1; // 代表 dp[i-2]
    let mut prev1: i32 = 1; // 代表 dp[i-1]
    let mut cur: i32 = 0;

    let mut i: i32 = 2;
    while i <= n {
        cur = prev1 + prev2;
        prev2 = prev1;
        prev1 = cur;
        i += 1;
    }
    return cur;
}
```

## 说明

这段代码使用滚动变量实现斐波那契式动态规划：
- `prev2` 保存到前两阶的方法数
- `prev1` 保存到前一阶的方法数
- `cur` 保存当前阶的方法数

最终返回爬到第 `n` 阶的方法总数。
