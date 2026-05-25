# Merge Sorted Arrays

## 问题描述

实现一个函数，输入两个非递减整数数组 `a`、`b`，长度分别为 `n`、`m`，把合并后的非递减结果写入长度为 `n + m` 的输出数组 `out`。

约定：

- `n >= 0`
- `m >= 0`
- `a` 的长度恰好是 `n`
- `b` 的长度恰好是 `m`
- `out` 的长度恰好是 `n + m`
- `a` 和 `b` 都非递减
- 函数不修改 `a` 和 `b`

## 参考实现

```rust
pub fn merge_sorted_arrays(n: i32, a: &[i32], m: i32, b: &[i32], out: &mut [i32]) {
    let mut i: i32 = 0;
    let mut j: i32 = 0;
    let mut k: i32 = 0;

    while i < n && j < m {
        if a[(i) as usize] <= b[(j) as usize] {
            out[(k) as usize] = a[(i) as usize];
            i += 1;
        } else {
            out[(k) as usize] = b[(j) as usize];
            j += 1;
        }
        k += 1;
    }

    while i < n {
        out[(k) as usize] = a[(i) as usize];
        i += 1;
        k += 1;
    }

    while j < m {
        out[(k) as usize] = b[(j) as usize];
        j += 1;
        k += 1;
    }
}
```

## 说明

这是经典归并过程，适合验证“三指针 + 输出前缀合并语义”。
