# String Has Double Char

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`，判断是否存在两个相邻字符相同。如果存在返回 `1`，否则返回 `0`。

约定：

- 输入是合法的 C 风格字符串
- 函数不修改字符串
- 返回值只使用 `0` 或 `1`

## 参考实现

```rust
pub fn string_has_double_char(s: &[u8]) -> i32 {
    let mut i: i32 = 1;

    while s[(i) as usize] != b'\0' {
        if s[(i) as usize] == s[(i - 1) as usize] {
            return 1;
        }
        i += 1;
    }

    return 0;
}
```

## 说明

这道题适合验证“字符串相邻字符关系 + 提前返回”模式。
