# Array Has Adjacent Equal

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，判断是否存在相邻两个元素相等。如果存在返回 `1`，否则返回 `0`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数不修改数组
- 返回值只使用 `0` 或 `1`

## 参考实现

```rust
pub fn array_has_adjacent_equal(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;

    i = 1;
    while i < n {
        if a[(i) as usize] == a[(i - 1) as usize] {
            return 1;
        }
        i += 1;
    }

    return 0;
}
```

## 说明

这道题适合验证“相邻元素关系 + 提前返回”模式。
