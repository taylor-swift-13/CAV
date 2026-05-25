# Array Clamp Nonnegative

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`。把所有负数元素改成 `0`，非负元素保持不变。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 需要原地修改数组

## 参考实现

```rust
pub fn array_clamp_nonnegative(n: i32, a: &mut [i32]) {
    let mut i: i32;

    i = 0;
    while i < n {
        if a[(i) as usize] < 0 {
            a[(i) as usize] = 0;
        }
        i += 1;
    }
}
```

## 说明

这道题适合验证“条件式原地修正”模式。
