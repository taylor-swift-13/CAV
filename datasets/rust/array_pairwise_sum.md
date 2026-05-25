# Array Pairwise Sum

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和 `b`，以及长度为 `n` 的输出数组 `out`。对每个下标 `i`，写入 `out[i] = a[i] + b[i]`。

约定：

- `n >= 0`
- `a`、`b` 和 `out` 的长度都恰好是 `n`
- 函数不修改 `a` 和 `b`

## 参考实现

```rust
pub fn array_pairwise_sum(n: i32, a: &[i32], b: &[i32], out: &mut [i32]) {
    let mut i: i32;

    i = 0;
    while i < n {
        out[(i) as usize] = a[(i) as usize] + b[(i) as usize];
        i += 1;
    }
}
```

## 说明

这道题适合验证“两个输入数组逐点计算输出数组”模式。
