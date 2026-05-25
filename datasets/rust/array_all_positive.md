# Array All Positive

## 问题描述

实现一个函数，判断长度为 `n` 的整数数组 `a` 是否全部大于 `0`。

约定：

- 如果所有元素都大于 `0`，返回 `1`
- 只要有一个元素小于等于 `0`，返回 `0`
- 函数不修改数组

## 参考实现

```rust
pub fn array_all_positive(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;

    i = 0;
    while i < n {
        if a[(i) as usize] <= 0 {
            return 0;
        }
        i += 1;
    }

    return 1;
}
```

## 说明

这道题是最基础的全称检查题：

- 单层循环
- 循环内早返回
- 不修改数组
