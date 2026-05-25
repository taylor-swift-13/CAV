# Array Copy Even

## 问题描述

实现一个函数，把输入数组中的偶数复制到输出数组同位置，奇数位置写 `0`。

约定：

- `n >= 0`。
- `a` 和 `out` 长度至少为 `n`。
- 不修改输入数组。

## 参考实现

```rust
pub fn array_copy_even(n: i32, a: &[i32], out: &mut [i32]) {
    let mut i = 0;
    while i < n {
        if a[i as usize] % 2 == 0 { out[i as usize] = a[i as usize]; }
        else { out[i as usize] = 0; }
        i += 1;
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
