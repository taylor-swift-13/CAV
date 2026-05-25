# String All Uppercase

## 问题描述

实现一个函数，判断 C 风格字符串是否全部由 ASCII 大写字母组成。

约定：

- 输入是以 `\0` 结尾的字符串。
- 空字符串返回 `1`。
- 非大写字母字符会导致返回 `0`。

## 参考实现

```rust
pub fn string_all_uppercase(s: &[u8]) -> i32 {
    let mut i = 0;
    while s[i as usize] != b'\0' { if s[i as usize] < b'A' || s[i as usize] > b'Z' { return 0; } i += 1; }
    1
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
