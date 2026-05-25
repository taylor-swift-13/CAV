# Rotate Left By One

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，把它循环左移一位。

约定：

- `n >= 1`
- 数组长度恰好是 `n`
- 需要原地修改数组
- 执行后：
  - 原来的 `a[1]` 变成新的 `a[0]`
  - 原来的 `a[n - 1]` 变成新的 `a[n - 2]`
  - 原来的 `a[0]` 变成新的 `a[n - 1]`

## 参考实现

```rust
pub fn rotate_left_by_one(n: i32, a: &mut [i32]) {
    let mut i: i32;
    let mut first: i32 = a[(0) as usize];

    i = 0;
    while i + 1 < n {
        a[(i) as usize] = a[(i + 1) as usize];
        i += 1;
    }
    a[(n - 1) as usize] = first;
}
```

## 说明

这道题适合验证“原地覆盖 + 最后补回暂存值”模式。
