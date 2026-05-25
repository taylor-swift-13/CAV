# Array Scale

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`、一个整数 `k`，以及长度为 `n` 的输出数组 `out`。把 `a` 中每个元素乘以 `k` 后写入 `out`。

约定：

- `n >= 0`
- `a` 和 `out` 长度都恰好是 `n`
- 函数不返回值
- 对每个下标 `i`，执行后都有 `out[i] == a[i] * k`

## 参考实现

```rust
pub fn array_scale(n: i32, a: &[i32], k: i32, out: &mut [i32]) {
    let mut i: i32;

    i = 0;
    while i < n {
        out[(i) as usize] = a[(i) as usize] * k;
        i += 1;
    }
}
```

## 说明

这道题适合验证“只读输入数组 + 标量参数 + 输出数组”的基础循环模式。
