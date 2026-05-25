# Is Prime Simple

## 问题描述

实现一个函数，输入整数 `n`，判断 `n` 是否为质数。如果是返回 `1`，否则返回 `0`。

约定：

- `n >= 0`
- 质数定义为大于 `1` 且只有 `1` 和自身两个正因子的整数
- 返回值只使用 `0` 或 `1`

## 参考实现

```rust
pub fn is_prime_simple(n: i32) -> i32 {
    let mut d: i32;

    if n < 2 {
        return 0;
    }

    d = 2;
    while d < n {
        if n % d == 0 {
            return 0;
        }
        d += 1;
    }

    return 1;
}
```

## 说明

这是最简单的质数判断，适合验证“逐个排除因子 + 提前返回”。
