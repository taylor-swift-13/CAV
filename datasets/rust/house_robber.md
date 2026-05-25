# House Robber

## 问题描述

实现一个函数，输入长度为 `n` 的非负整数数组 `a`，返回在不能选择相邻元素的限制下可以得到的最大和。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 所有 `a[i] >= 0`
- 函数不修改数组

## 参考实现

```rust
pub fn house_robber(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut prev2: i32 = 0;
    let mut prev1: i32 = 0;
    let mut take: i32;
    let mut cur: i32;

    i = 0;
    while i < n {
        take = prev2 + a[(i) as usize];
        if take > prev1 {
            cur = take;
        } else {
            cur = prev1;
        }
        prev2 = prev1;
        prev1 = cur;
        i += 1;
    }

    return prev1;
}
```

## 说明

这是最经典的一维 DP 题，适合验证“前一项最优”和“前两项最优”的滚动状态。
