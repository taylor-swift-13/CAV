# Array Second Largest

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回其中第二大的元素。

约定：

- `n >= 2`
- 数组长度恰好是 `n`
- 可以假设数组中所有元素互不相同
- 函数不修改数组

## 参考实现

```rust
pub fn array_second_largest(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut max1: i32 = a[(0) as usize];
    let mut max2: i32 = a[(1) as usize];

    if max2 > max1 {
        let mut t: i32 = max1;
        max1 = max2;
        max2 = t;
    }

    i = 2;
    while i < n {
        if a[(i) as usize] > max1 {
            max2 = max1;
            max1 = a[(i) as usize];
        } else if a[(i) as usize] > max2 {
            max2 = a[(i) as usize];
        }
        i += 1;
    }

    return max2;
}
```

## 说明

这道题适合验证“双状态量扫描”模式：

- 同时维护最大值和次大值
- 分支更新比单纯 max/min 更复杂
