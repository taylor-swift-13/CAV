# String Count Hash

## 问题描述

实现一个函数，统计 C 风格字符串中 `#` 字符的数量。

约定：

- 输入是以 `\0` 结尾的字符串。
- 只统计 ASCII `#`。
- 空字符串返回 `0`。

## 参考实现

```rust
pub fn string_count_hash(s: &[u8]) -> i32 {
    let mut count = 0;
    let mut i = 0;
    while s[i as usize] != b'\0' { if s[i as usize] == b'#' { count += 1; } i += 1; }
    count
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
