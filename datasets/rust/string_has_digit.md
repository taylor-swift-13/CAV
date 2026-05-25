# String Has Digit

## 问题描述

实现一个函数，判断 C 风格字符串中是否存在 ASCII 数字。

约定：

- 输入是以 `\0` 结尾的字符串。
- 存在 `'0'..'9'` 返回 `1`。
- 否则返回 `0`。

## 参考实现

```rust
pub fn string_has_digit(s: &[u8]) -> i32 {
    let mut i = 0;
    while s[i as usize] != b'\0' { if s[i as usize] >= b'0' && s[i as usize] <= b'9' { return 1; } i += 1; }
    0
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
