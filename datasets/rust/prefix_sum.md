# Prefix Sum

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和长度为 `n` 的整数数组 `out`，把前缀和写入 `out`。

约定：

- `n >= 0`
- `a` 和 `out` 长度都恰好是 `n`
- `out[i] = a[0] + a[1] + ... + a[i]`

## 参考实现

```rust
pub fn prefix_sum(n: i32, a: &[i32], out: &mut [i32]) {
    let mut i: i32;
    let mut acc: i32 = 0;

    i = 0;
    while i < n {
        acc += a[(i) as usize];
        out[(i) as usize] = acc;
        i += 1;
    }
}
```

## 说明

这道题是最基础的前缀和构造：

- 单层循环
- 一个累加器
- 读数组并写数组
