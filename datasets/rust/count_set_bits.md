# Count Set Bits

## 问题描述

实现一个函数，返回非负整数 `n` 的二进制表示中 `1` 的个数。

约定：

- `n >= 0`。
- `n == 0` 时返回 `0`。
- 只需要处理 32 位非负整数。

## 参考实现

```rust
pub fn count_set_bits(mut n: i32) -> i32 {
    let mut count = 0;
    while n > 0 {
        if n % 2 == 1 { count += 1; }
        n /= 2;
    }
    count
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
