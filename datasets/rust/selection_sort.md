# Selection Sort

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，用选择排序将数组原地排成非递减顺序。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数原地修改数组

## 参考实现

```rust
pub fn selection_sort(n: i32, a: &mut [i32]) {
    let mut i: i32;
    let mut j: i32;
    let mut min_idx: i32;
    let mut tmp: i32;

    i = 0;
    while i < n {
        min_idx = i;
        j = i + 1;
        while j < n {
            if a[(j) as usize] < a[(min_idx) as usize] {
                min_idx = j;
            }
            j += 1;
        }
        tmp = a[(i) as usize];
        a[(i) as usize] = a[(min_idx) as usize];
        a[(min_idx) as usize] = tmp;
        i += 1;
    }
}
```

## 说明

这是经典简单排序题，适合验证“已排序前缀 + 剩余区间最小值选择”。
