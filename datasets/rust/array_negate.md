# Array Negate

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和长度为 `n` 的输出数组 `out`。把每个元素取相反数后写入 `out`。

约定：

- `n >= 0`
- 两个数组长度都恰好是 `n`
- 函数不返回值
- 对每个下标 `i`，执行后都有 `out[i] == -a[i]`

## 参考实现

```rust
pub fn array_negate(n: i32, a: &[i32], out: &mut [i32]) {
    let mut i: i32;

    i = 0;
    while i < n {
        out[(i) as usize] = -a[(i) as usize];
        i += 1;
    }
}
```

## 说明

这道题适合验证“逐元素一元变换”的数组输出模式。
