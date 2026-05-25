# Array None Zero

## 问题描述

实现一个函数，判断长度为 `n` 的整数数组中是否没有零。

约定：

- `n >= 0`。
- 没有零返回 `1`。
- 存在零返回 `0`。
- 空数组返回 `1`。

## 参考实现

```rust
pub fn array_none_zero(n: i32, a: &[i32]) -> i32 {
    let mut i = 0;
    while i < n { if a[i as usize] == 0 { return 0; } i += 1; }
    1
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
