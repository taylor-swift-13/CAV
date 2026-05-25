# String Replace Spaces Underscore

## 问题描述

实现一个函数，把 C 风格字符串中的空格原地替换为下划线。

约定：

- 输入是以 `\0` 结尾的可变字符串。
- 只替换 ASCII 空格 `' '`。
- 字符串长度不变。

## 参考实现

```rust
pub fn string_replace_spaces_underscore(s: &mut [u8]) {
    let mut i = 0;
    while s[i as usize] != b'\0' { if s[i as usize] == b' ' { s[i as usize] = b'_'; } i += 1; }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
