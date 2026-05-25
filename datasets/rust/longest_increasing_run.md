# Longest Increasing Run

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回最长连续严格递增段的长度。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 空数组的结果为 `0`
- 函数不修改数组

## 参考实现

```rust
pub fn longest_increasing_run(mut n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut cur: i32;
    let mut best: i32;

    if n == 0 {
        return 0;
    }

    cur = 1;
    best = 1;
    i = 1;
    while i < n {
        if a[(i - 1) as usize] < a[(i) as usize] {
            cur += 1;
        } else {
            cur = 1;
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

这是经典线性 DP/扫描题，适合验证“当前连续段长度 + 历史最优长度”。
