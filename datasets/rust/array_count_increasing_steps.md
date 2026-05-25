# Array Count Increasing Steps

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，统计满足 `a[i] < a[i + 1]` 的下标个数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组

## 参考实现

```rust
pub fn array_count_increasing_steps(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut cnt: i32 = 0;

    i = 0;
    while i + 1 < n {
        if a[(i) as usize] < a[(i + 1) as usize] {
            cnt += 1;
        }
        i += 1;
    }

    return cnt;
}
```

## 说明

这道题适合验证“相邻比较 + 条件计数”模式。
