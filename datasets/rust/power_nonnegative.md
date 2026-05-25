# Power Nonnegative

## 问题描述

实现一个函数，输入整数 `base` 和非负整数 `exp`，返回 `base` 的 `exp` 次方。

约定：

- `exp >= 0`
- `base^0 = 1`
- 使用简单循环乘法，不使用快速幂

## 参考实现

```rust
pub fn power_nonnegative(base: i32, exp: i32) -> i32 {
    let mut i: i32;
    let mut ans: i32 = 1;

    i = 0;
    while i < exp {
        ans = ans * base;
        i += 1;
    }

    return ans;
}
```

## 说明

这是最简单的幂运算题，适合验证“循环次数与累乘状态量”。
