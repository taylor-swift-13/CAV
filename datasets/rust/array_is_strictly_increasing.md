# Array Is Strictly Increasing

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，判断数组是否严格递增。如果对所有相邻下标都有 `a[i - 1] < a[i]`，返回 `1`，否则返回 `0`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 空数组和单元素数组都视为严格递增
- 函数不修改数组

## 参考实现

```rust
pub fn array_is_strictly_increasing(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;

    i = 1;
    while i < n {
        if a[(i - 1) as usize] >= a[(i) as usize] {
            return 0;
        }
        i += 1;
    }

    return 1;
}
```

## 说明

这道题适合验证“相邻有序性 + 反例提前返回”模式。
