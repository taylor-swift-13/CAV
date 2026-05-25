# Array Index Of Min

## 问题描述

实现一个函数，返回长度为 `n` 的非空整数数组中最小值第一次出现的位置。

约定：

- `n > 0`。
- 数组长度至少为 `n`。
- 如果最小值出现多次，返回最小下标。

## 参考实现

```rust
pub fn array_index_of_min(n: i32, a: &[i32]) -> i32 {
    let mut idx = 0;
    let mut i = 1;
    while i < n {
        if a[i as usize] < a[idx as usize] { idx = i; }
        i += 1;
    }
    idx
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
