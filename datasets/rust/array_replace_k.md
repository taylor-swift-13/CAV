# Array Replace K

## 问题描述

实现一个函数，输入长度为 `n` 的整数数组 `a`、整数 `old_k` 和 `new_k`，把数组中所有等于 `old_k` 的元素替换成 `new_k`。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 需要原地修改数组

## 参考实现

```rust
pub fn array_replace_k(n: i32, a: &mut [i32], old_k: i32, new_k: i32) {
    let mut i: i32;

    i = 0;
    while i < n {
        if a[(i) as usize] == old_k {
            a[(i) as usize] = new_k;
        }
        i += 1;
    }
}
```

## 说明

这道题适合验证“条件式原地更新”模式：

- 不是每轮都写
- 更新逻辑取决于当前元素是否命中
