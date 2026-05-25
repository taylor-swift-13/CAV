# Array First Peak

## 问题描述

实现一个函数，返回数组中第一个峰值位置。

约定：
- `n` 表示数组长度，`n >= 0`。
- `a` 指向长度至少为 `n` 的整数数组。
- 峰值位置 `i` 必须满足 `0 < i < n - 1`，并且 `a[i] >= a[i - 1]` 且 `a[i] >= a[i + 1]`。
- 如果不存在峰值位置，返回 `-1`。

## 参考实现

```rust
pub fn array_first_peak(n: i32, a: &[i32]) -> i32 {
    let mut i: i32 = 1;
    while i + 1 < n {
        if a[(i) as usize] >= a[(i - 1) as usize] && a[(i) as usize] >= a[(i + 1) as usize] {
            return i;
        }
        i += 1;
    }
    return -1;
}
```

## 说明

峰值不能出现在数组两端，因此扫描从下标 `1` 开始，到 `n - 2` 结束。第一次满足条件的位置就是答案。
