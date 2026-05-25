# Is Sorted Nondecreasing

## 问题描述

实现一个函数，判断长度为 `n` 的整数数组 `a` 是否是非递减的。

约定：

- 如果对所有 `0 <= i < n - 1` 都有 `a[i] <= a[i + 1]`，返回 `1`
- 否则返回 `0`
- 函数不修改数组

## 参考实现

```rust
pub fn is_sorted_nondecreasing(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;

    i = 0;
    while i + 1 < n {
        if a[(i) as usize] > a[(i + 1) as usize] {
            return 0;
        }
        i += 1;
    }

    return 1;
}
```

## 说明

这道题适合验证“扫描直到发现反例”的模式：

- 单层循环
- 循环内早返回
- 不修改数组
