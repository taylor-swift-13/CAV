# Binary Search

## 问题描述

实现一个函数，输入长度为 `n` 的非递减整数数组 `a` 和目标值 `target`，如果目标值存在，返回任意一个等于 `target` 的下标；如果不存在，返回 `-1`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 数组 `a` 非递减
- 函数不修改数组

## 参考实现

```rust
pub fn binary_search(n: i32, a: &[i32], target: i32) -> i32 {
    let mut left: i32 = 0;
    let mut right: i32 = n - 1;
    let mut mid: i32;

    while left <= right {
        mid = left + (right - left) / 2;
        if a[(mid) as usize] == target {
            return mid;
        }
        if a[(mid) as usize] < target {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }

    return -1;
}
```

## 说明

这是最基础的二分查找题，适合验证“搜索区间收缩 + 区间外排除性质”。
