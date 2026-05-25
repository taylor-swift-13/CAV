# Max Subarray Sum

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回非空连续子数组的最大和。

约定：

- `n >= 1`
- `a` 的长度恰好是 `n`
- 函数不修改数组
- 使用 Kadane 算法

## 参考实现

```rust
pub fn max_subarray_sum(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut cur: i32 = a[(0) as usize];
    let mut best: i32 = a[(0) as usize];

    i = 1;
    while i < n {
        if cur + a[(i) as usize] < a[(i) as usize] {
            cur = a[(i) as usize];
        } else {
            cur = cur + a[(i) as usize];
        }
        if best < cur {
            best = cur;
        }
        i += 1;
    }

    return best;
}
```

## 说明

这是经典 Kadane 动态规划题，适合验证“当前后缀最优 + 全局最优”两个状态量。
