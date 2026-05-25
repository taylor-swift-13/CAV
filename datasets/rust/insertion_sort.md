# Insertion Sort

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，用插入排序将数组原地排成非递减顺序。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数原地修改数组

## 参考实现

```rust
pub fn insertion_sort(n: i32, a: &mut [i32]) {
    let mut i: i32;
    let mut j: i32;
    let mut key: i32;

    i = 1;
    while i < n {
        key = a[(i) as usize];
        j = i - 1;
        while j >= 0 && a[(j) as usize] > key {
            a[(j + 1) as usize] = a[(j) as usize];
            j -= 1;
        }
        a[(j + 1) as usize] = key;
        i += 1;
    }
}
```

## 说明

这是经典插入排序题，适合验证“有序前缀 + 元素右移 + 插入位置”。
