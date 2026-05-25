# Sum To N

## 问题描述

实现一个函数，输入正整数 `n`，返回 `1 + 2 + ... + n` 的结果。

约定：

- `n >= 0`
- 结果保证在 32 位有符号整数范围内
- 函数不读写任何额外内存

## 参考实现

```rust
pub fn sum_to_n(n: i32) -> i32 {
    let mut i: i32;
    let mut ret: i32 = 0;

    i = 1;
    while i <= n {
        ret += i;
        i += 1;
    }

    return ret;
}
```

## 说明

这是一道最基础的循环累加题：

- 单层循环
- 标量状态
- 没有数组
- invariant 适合写成“`ret` 等于前 `i - 1` 个正整数之和”
