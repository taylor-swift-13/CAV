# Array Add

## 问题描述

实现一个函数，输入两个长度为 `n` 的整数数组 `a`、`b`，以及长度为 `n` 的输出数组 `out`。把逐项求和结果写入 `out`。

约定：

- `n >= 0`
- 三个数组长度都恰好是 `n`
- 函数不返回值
- 对每个下标 `i`，执行后都有 `out[i] == a[i] + b[i]`

## 参考实现

```rust
pub fn array_add(n: i32, a: &[i32], b: &[i32], out: &mut [i32]) {
    let mut i: i32;

    i = 0;
    while i < n {
        out[(i) as usize] = a[(i) as usize] + b[(i) as usize];
        i += 1;
    }
}
```

## 说明

这道题适合验证“两个输入数组 + 一个输出数组”的最基础写入模式：

- 单层循环
- 输出数组逐步填充
- 输入数组保持不变
