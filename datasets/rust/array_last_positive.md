# Array Last Positive

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回最后一个正数元素的下标；如果不存在正数，返回 `-1`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 函数不修改数组

## 参考实现

```rust
pub fn array_last_positive(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut ans: i32 = -1;

    i = 0;
    while i < n {
        if a[(i) as usize] > 0 {
            ans = i;
        }
        i += 1;
    }

    return ans;
}
```

## 说明

这道题适合验证“扫描状态量保存最后一次命中位置”模式。
