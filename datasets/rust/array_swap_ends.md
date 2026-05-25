# Array Swap Ends

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`。如果 `n >= 2`，交换首元素和尾元素；否则保持不变。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 需要原地修改数组

## 参考实现

```rust
pub fn array_swap_ends(n: i32, a: &mut [i32]) {
    let mut t: i32;

    if n < 2 {
        return;
    }

    t = a[(0) as usize];
    a[(0) as usize] = a[(n - 1) as usize];
    a[(n - 1) as usize] = t;
}
```

## 说明

这道题适合验证“短分支 + 常量次更新”模式。
