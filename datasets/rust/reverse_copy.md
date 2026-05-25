# Reverse Copy

## 问题描述

实现一个函数，把长度为 `n` 的整数数组 `src` 逆序复制到长度为 `n` 的整数数组 `dst`。

约定：

- `n >= 0`
- `src` 和 `dst` 长度都恰好是 `n`
- 函数读取 `src`，写入 `dst`

## 参考实现

```rust
pub fn reverse_copy(n: i32, src: &[i32], dst: &mut [i32]) {
    let mut i: i32;

    i = 0;
    while i < n {
        dst[(i) as usize] = src[(n - 1 - i) as usize];
        i += 1;
    }
}
```

## 说明

这道题是最基础的逆序数组构造：

- 单层循环
- 一个读、一个写
- 不修改源数组
