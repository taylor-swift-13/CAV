# Array Any Negative

## 问题描述

实现一个函数，判断长度为 `n` 的整数数组中是否存在负数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组
- 如果存在某个下标 `i` 满足 `a[i] < 0`，返回 `1`
- 否则返回 `0`

## 参考实现

```rust
pub fn array_any_negative(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;

    i = 0;
    while i < n {
        if a[(i) as usize] < 0 {
            return 1;
        }
        i += 1;
    }

    return 0;
}
```

## 说明

这道题适合验证“数组扫描 + 早返回”的存在性判断模式。
