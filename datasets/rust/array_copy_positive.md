# Array Copy Positive

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和长度为 `n` 的输出数组 `out`。如果 `a[i]` 是正数，则 `out[i] = a[i]`；否则 `out[i] = 0`。

约定：

- `n >= 0`
- `a` 和 `out` 的长度都恰好是 `n`
- 函数不修改 `a`

## 参考实现

```rust
pub fn array_copy_positive(n: i32, a: &[i32], out: &mut [i32]) {
    let mut i: i32;

    i = 0;
    while i < n {
        if a[(i) as usize] > 0 {
            out[(i) as usize] = a[(i) as usize];
        } else {
            out[(i) as usize] = 0;
        }
        i += 1;
    }
}
```

## 说明

这道题适合验证“输入数组到输出数组的条件映射”模式。
