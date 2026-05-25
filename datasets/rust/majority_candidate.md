# Majority Candidate

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回 Boyer-Moore 投票算法得到的候选多数元素。

约定：

- `n >= 1`
- `a` 的长度恰好是 `n`
- 题目只要求返回候选值，不要求在函数中验证它一定出现超过一半
- 函数不修改数组

## 参考实现

```rust
pub fn majority_candidate(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut candidate: i32 = a[(0) as usize];
    let mut count: i32 = 1;

    i = 1;
    while i < n {
        if count == 0 {
            candidate = a[(i) as usize];
            count = 1;
        } else if a[(i) as usize] == candidate {
            count += 1;
        } else {
            count -= 1;
        }
        i += 1;
    }

    return candidate;
}
```

## 说明

这是经典 Boyer-Moore 投票算法，适合验证“候选值 + 抵消计数”的状态更新。
