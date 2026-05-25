# Array Count Even

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回其中偶数元素的个数。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数不修改数组
- 使用 `x % 2 == 0` 判断偶数

## 参考实现

```rust
pub fn array_count_even(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut cnt: i32 = 0;

    i = 0;
    while i < n {
        if a[(i) as usize] % 2 == 0 {
            cnt += 1;
        }
        i += 1;
    }

    return cnt;
}
```

## 说明

这道题适合验证“数组扫描 + 条件计数”模式。
