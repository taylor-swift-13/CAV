# Count Divisors

## 问题描述

实现一个函数，输入正整数 `n`，返回 `n` 的正约数个数。

约定：

- `n >= 1`
- 如果 `d` 满足 `1 <= d <= n` 且 `n % d == 0`，则 `d` 是 `n` 的正约数

## 参考实现

```rust
pub fn count_divisors(n: i32) -> i32 {
    let mut d: i32;
    let mut cnt: i32 = 0;

    d = 1;
    while d <= n {
        if n % d == 0 {
            cnt += 1;
        }
        d += 1;
    }

    return cnt;
}
```

## 说明

这是最简单的约数计数题，适合验证“数论条件计数 + 循环边界”。
