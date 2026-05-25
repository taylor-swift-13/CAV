# Remove Duplicates Sorted

## 问题描述

实现一个函数，输入长度为 `n` 的非递减整数数组 `a`，原地删除重复元素，使每个不同元素只保留一次，并返回新长度。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 数组 `a` 非递减
- 函数可以修改数组前缀

## 参考实现

```rust
pub fn remove_duplicates_sorted(mut n: i32, a: &mut [i32]) -> i32 {
    let mut i: i32;
    let mut j: i32;

    if n == 0 {
        return 0;
    }

    j = 1;
    i = 1;
    while i < n {
        if a[(i) as usize] != a[(j - 1) as usize] {
            a[(j) as usize] = a[(i) as usize];
            j += 1;
        }
        i += 1;
    }

    return j;
}
```

## 说明

这是经典双指针原地压缩题，适合验证“输出前缀是不重复摘要”。
