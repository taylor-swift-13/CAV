# Array Minimum

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`，返回数组中的最小值。

约定：

- `n >= 1`
- 数组长度恰好是 `n`
- 函数只读数组，不修改数组内容

## 参考实现

```rust
pub fn array_min(n: i32, a: &[i32]) -> i32 {
    let mut i: i32;
    let mut ret: i32 = a[(0) as usize];

    i = 1;
    while i < n {
        if a[(i) as usize] < ret {
            ret = a[(i) as usize];
        }
        i += 1;
    }

    return ret;
}
```

## 说明

这道题和 `array_max` 对称：

- 单层循环
- 循环内一个分支
- 不修改数组
- invariant 适合写成“`ret` 是当前已扫描前缀的最小值”
