# Min Cost Two Steps

## 问题描述

实现一个函数，输入长度为 `n` 的非负整数数组 `cost`，每次可以向前走一步或两步，返回走到下标 `n - 1` 的最小代价。进入下标 `i` 的代价是 `cost[i]`。

约定：

- `n >= 1`
- `cost` 的长度恰好是 `n`
- 所有 `cost[i] >= 0`
- 起点在下标 `0`
- 函数不修改数组

## 参考实现

```rust
pub fn min_cost_two_steps(mut n: i32, cost: &[i32]) -> i32 {
    let mut i: i32;
    let mut prev2: i32;
    let mut prev1: i32;
    let mut cur: i32;

    if n == 1 {
        return cost[(0) as usize];
    }

    prev2 = cost[(0) as usize];
    prev1 = cost[(0) as usize] + cost[(1) as usize];

    i = 2;
    while i < n {
        if prev1 < prev2 {
            cur = prev1 + cost[(i) as usize];
        } else {
            cur = prev2 + cost[(i) as usize];
        }
        prev2 = prev1;
        prev1 = cur;
        i += 1;
    }

    return prev1;
}
```

## 说明

这是最简单的线性 DP 最小值问题，适合验证“状态量表示前两个位置最优解”。
