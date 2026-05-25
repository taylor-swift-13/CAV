# Array Fill Value

## 问题描述

实现一个函数，把数组前 `n` 个位置全部原地写成给定值 `k`。

约定：

- `n >= 0`。
- 数组长度至少为 `n`。
- 只修改前 `n` 个元素。

## 参考实现

```rust
pub fn array_fill_value(n: i32, k: i32, a: &mut [i32]) {
    let mut i = 0;
    while i < n {
        a[i as usize] = k;
        i += 1;
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
