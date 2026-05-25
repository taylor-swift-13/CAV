# Array Count Between

## 问题描述

实现一个函数，统计长度为 `n` 的整数数组中位于闭区间 `[lo, hi]` 内的元素个数。

约定：

- `n >= 0`。
- `lo <= hi`。
- 数组长度至少为 `n`。

## 参考实现

```rust
pub fn array_count_between(n: i32, a: &[i32], lo: i32, hi: i32) -> i32 {
    let mut i = 0;
    let mut count = 0;
    while i < n {
        if a[i as usize] >= lo && a[i as usize] <= hi { count += 1; }
        i += 1;
    }
    count
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
