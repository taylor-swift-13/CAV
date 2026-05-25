# String To Lower ASCII

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`，把其中的大写英文字母原地转换为小写英文字母，其他字符保持不变。

约定：

- 输入是合法的 C 风格字符串
- 只处理 ASCII 大写字母 `'A'` 到 `'Z'`
- 函数原地修改字符串

## 参考实现

```rust
pub fn string_to_lower_ascii(s: &mut [u8]) {
    let mut i: i32 = 0;

    while s[(i) as usize] != b'\0' {
        if s[(i) as usize] >= b'A' && s[(i) as usize] <= b'Z' {
            s[(i) as usize] = s[(i) as usize] + 32;
        }
        i += 1;
    }
}
```

## 说明

这道题适合验证“字符串原地更新 + 字符范围变换”模式。
