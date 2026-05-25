# Find First Equal

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和整数 `k`，返回第一个等于 `k` 的下标；如果不存在，返回 `-1`。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组

## 参考实现

```rust
pub fn find_first_equal(n: i32, a: &[i32], k: i32) -> i32 {
    let mut i: i32;

    i = 0;
    while i < n {
        if a[(i) as usize] == k {
            return i;
        }
        i += 1;
    }

    return -1;
}
```

## 说明

这道题适合验证最基础的“扫描直到命中”模式：

- 单层循环
- 循环内早返回
- 不修改数组
