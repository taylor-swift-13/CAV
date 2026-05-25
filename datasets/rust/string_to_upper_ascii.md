# String To Upper ASCII

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`，把其中所有小写字母转成大写字母，其他字符保持不变。

约定：

- 输入是合法的 C 风格字符串
- 需要原地修改字符串

## 参考实现

```rust
pub fn string_to_upper_ascii(s: &mut [u8]) {
    let mut i: i32 = 0;

    while s[(i) as usize] != b'\0' {
        if b'a' <= s[(i) as usize] && s[(i) as usize] <= b'z' {
            s[(i) as usize] = s[(i) as usize] - b'a' + b'A';
        }
        i += 1;
    }
}
```

## 说明

这道题适合验证“字符串扫描 + 条件原地更新”模式。
