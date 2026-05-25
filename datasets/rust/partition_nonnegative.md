# Partition Nonnegative

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，原地调整数组，使所有负数位于前面，所有非负数位于后面，返回负数的个数。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数原地修改数组
- 不要求保持元素原有相对顺序

## 参考实现

```rust
pub fn partition_nonnegative(n: i32, a: &mut [i32]) -> i32 {
    let mut i: i32 = 0;
    let mut j: i32 = n - 1;
    let mut tmp: i32;

    while i <= j {
        if a[(i) as usize] < 0 {
            i += 1;
        } else {
            tmp = a[(i) as usize];
            a[(i) as usize] = a[(j) as usize];
            a[(j) as usize] = tmp;
            j -= 1;
        }
    }

    return i;
}
```

## 说明

这是经典 partition 题，适合验证“双指针区间收缩 + 分区性质”。
