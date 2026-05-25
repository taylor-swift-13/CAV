# Array All Less Than K

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和整数 `k`，判断所有元素是否都严格小于 `k`。如果是返回 `1`，否则返回 `0`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 空数组视为满足条件
- 函数不修改数组

## 参考实现

```rust
pub fn array_all_less_than_k(n: i32, a: &[i32], k: i32) -> i32 {
    let mut i: i32;

    i = 0;
    while i < n {
        if a[(i) as usize] >= k {
            return 0;
        }
        i += 1;
    }

    return 1;
}
```

## 说明

这道题适合验证“数组全称性质 + 反例提前返回”模式。
