# Array Increment

## 问题描述

实现一个函数，把长度为 `n` 的整数数组 `a` 的每个元素都加一。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 每个元素加一后仍在 32 位有符号整数范围内
- 函数原地修改数组

## 参考实现

```rust
pub fn array_increment(n: i32, a: &mut [i32]) {
    let mut i: i32;

    i = 0;
    while i < n {
        a[(i) as usize] = a[(i) as usize] + 1;
        i += 1;
    }
}
```

## 说明

这道题比 `set_zero` 多一步读后写：

- 单层循环
- 原地更新
- 需要元素范围前置条件保证 `a[i] + 1` 不溢出
- invariant 适合写成“已处理前缀等于原数组前缀逐项加一”
