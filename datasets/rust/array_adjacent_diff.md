# Array Adjacent Diff

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和长度为 `n - 1` 的输出数组 `out`。对每个下标 `i`，写入 `out[i] = a[i + 1] - a[i]`。

约定：

- `n >= 1`
- `a` 的长度恰好是 `n`
- `out` 的长度恰好是 `n - 1`
- 函数不修改 `a`

## 参考实现

```rust
pub fn array_adjacent_diff(n: i32, a: &[i32], out: &mut [i32]) {
    let mut i: i32;

    i = 0;
    while i + 1 < n {
        out[(i) as usize] = a[(i + 1) as usize] - a[(i) as usize];
        i += 1;
    }
}
```

## 说明

这道题适合验证“相邻元素关系 + 输出数组写入”模式。
