# String Any Lowercase

## 问题描述

实现一个函数，判断 C 风格字符串中是否存在 ASCII 小写字母。

约定：

- 输入是以 `\0` 结尾的字符串。
- 存在 `'a'..'z'` 返回 `1`。
- 否则返回 `0`。

## 参考实现

```rust
pub fn string_any_lowercase(s: &[u8]) -> i32 {
    let mut i = 0;
    while s[i as usize] != b'\0' { if s[i as usize] >= b'a' && s[i as usize] <= b'z' { return 1; } i += 1; }
    0
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
