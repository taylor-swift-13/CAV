# Array All Zero

## 问题描述

实现一个函数，判断长度为 `n` 的整数数组是否全为 `0`。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组
- 如果所有元素都等于 `0`，返回 `1`
- 只要存在一个非零元素，返回 `0`

## 参考实现

```rust
pub fn array_all_zero(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;

    i = 0;
    while i < n {
        if a[(i) as usize] != 0 {
            return 0;
        }
        i += 1;
    }

    return 1;
}
```

## 说明

这道题适合验证“全称性质 + 反例早返回”的数组扫描模式。
