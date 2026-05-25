# String Collapse Spaces

## 问题描述

实现一个函数，把输入字符串中每一段连续空格压缩成一个空格，并写入输出字符串。

约定：
- `s` 是以 `'\0'` 结尾的输入字符串。
- `out` 指向足够大的输出缓冲区。
- 每一段一个或多个连续空格 `' '` 在输出中变成一个空格。
- 非空格字符保持原顺序。
- 输出字符串必须以 `'\0'` 结尾。

## 参考实现

```rust
pub fn string_collapse_spaces(s: &[u8], out: &mut [u8]) {
    let mut i: i32 = 0;
    let mut j: i32 = 0;
    let mut in_space: i32 = 0;
    while s[(i) as usize] != b'\0' {
        if s[(i) as usize] == b' ' {
            if in_space == 0 {
                out[(j) as usize] = b' ';
                j += 1;
                in_space = 1;
            }
        } else {
            out[(j) as usize] = s[(i) as usize];
            j += 1;
            in_space = 0;
        }
        i += 1;
    }
    out[(j) as usize] = b'\0';
}
```

## 说明

`in_space` 记录上一段输出是否已经写过空格。遇到连续空格时只写入第一个空格，遇到非空格字符时正常复制并清除空格状态。
