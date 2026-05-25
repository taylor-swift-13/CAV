# Array Sign

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a` 和长度为 `n` 的输出数组 `out`。对每个元素，正数写 `1`，负数写 `-1`，零写 `0`。

约定：

- `n >= 0`
- `a` 和 `out` 的长度都恰好是 `n`
- 函数不修改 `a`

## 参考实现

```rust
pub fn array_sign(n: i32, a: &[i32], out: &mut [i32]) {
    let mut i: i32;

    i = 0;
    while i < n {
        if a[(i) as usize] > 0 {
            out[(i) as usize] = 1;
        } else if a[(i) as usize] < 0 {
            out[(i) as usize] = -1;
        } else {
            out[(i) as usize] = 0;
        }
        i += 1;
    }
}
```

## 说明

这道题适合验证“数组条件分类 + 多分支输出”模式。
