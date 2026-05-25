# Array Sum Even Indices

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回所有偶数下标元素的和。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数不修改数组
- 偶数下标指 `0, 2, 4, ...`

## 参考实现

```rust
pub fn array_sum_even_indices(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut sum: i32 = 0;

    i = 0;
    while i < n {
        if i % 2 == 0 {
            sum += a[(i) as usize];
        }
        i += 1;
    }

    return sum;
}
```

## 说明

这道题适合验证“数组扫描 + 下标条件 + 累加器”模式。
