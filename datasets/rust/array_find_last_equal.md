# Array Find Last Equal

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和整数 `k`，返回最后一个满足 `a[i] == k` 的下标。如果不存在这样的元素，返回 `-1`。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组
- 如果存在多个匹配位置，返回最大的匹配下标

## 参考实现

```rust
pub fn array_find_last_equal(n: i32, a: &[i32], k: i32) -> i32 {
    let mut i: i32;
    let mut ans: i32 = -1;

    i = 0;
    while i < n {
        if a[(i) as usize] == k {
            ans = i;
        }
        i += 1;
    }

    return ans;
}
```

## 说明

这道题适合验证“扫描并维护最后一次命中位置”的模式。
