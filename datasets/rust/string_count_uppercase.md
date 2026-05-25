# String Count Uppercase

## 问题描述

实现一个函数，统计 C 风格字符串中 ASCII 大写字母的数量。

约定：

- 输入是以 `\0` 结尾的字符串。
- 只统计 `'A'` 到 `'Z'`。
- 空字符串返回 `0`。

## 参考实现

```rust
pub fn string_count_uppercase(s: &[u8]) -> i32 {
    let mut i = 0;
    let mut count = 0;
    while s[i as usize] != b'\0' {
        if s[i as usize] >= b'A' && s[i as usize] <= b'Z' { count += 1; }
        i += 1;
    }
    count
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
