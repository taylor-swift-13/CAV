# Array Count Transitions

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，统计相邻元素发生变化的次数。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数不修改数组
- 对每个 `i >= 1`，如果 `a[i] != a[i - 1]`，则计数加一

## 参考实现

```rust
pub fn array_count_transitions(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut cnt: i32 = 0;

    i = 1;
    while i < n {
        if a[(i) as usize] != a[(i - 1) as usize] {
            cnt += 1;
        }
        i += 1;
    }

    return cnt;
}
```

## 说明

这道题适合验证“相邻元素比较 + 条件计数”模式。
