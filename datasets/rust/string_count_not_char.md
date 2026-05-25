# String Count Not Char

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s` 和字符 `c`，统计字符串中不等于 `c` 的字符个数。

约定：

- 字符串是合法的 C 风格字符串
- 函数不修改字符串
- 只统计终止符之前的字符
- 返回值等于满足 `s[i] != c` 的字符数量

## 参考实现

```rust
pub fn string_count_not_char(s: &[u8], c: u8) -> i32 {
    let mut i: i32 = 0;
    let mut count: i32 = 0;

    while s[(i) as usize] != b'\0' {
        if s[(i) as usize] != c {
            count += 1;
        }
        i += 1;
    }

    return count;
}
```

## 说明

这道题适合验证“字符串扫描 + 条件计数”的模式。
