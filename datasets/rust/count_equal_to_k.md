# Count Equal To K

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和整数 `k`，返回数组中等于 `k` 的元素个数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 函数不修改数组

## 参考实现

```rust
pub fn count_equal_to_k(n: i32, a: &[i32], k: i32) -> i32 {
    let mut i: i32;
    let mut ret: i32 = 0;

    i = 0;
    while i < n {
        if a[(i) as usize] == k {
            ret += 1;
        }
        i += 1;
    }

    return ret;
}
```

## 说明

这道题是最基础的数组计数题：

- 单层循环
- 循环内一个分支
- 不修改数组
