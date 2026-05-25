# String Find Char

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s` 和字符 `c`，返回 `c` 第一次出现的位置；如果不存在，返回 `-1`。

约定：

- 输入是合法的 C 风格字符串
- 函数不修改字符串

## 参考实现

```rust
pub fn string_find_char(s: &[u8], c: u8) -> i32 {
    let mut i: i32 = 0;

    while s[(i) as usize] != b'\0' {
        if s[(i) as usize] == c {
            return i;
        }
        i += 1;
    }

    return -1;
}
```

## 说明

这道题适合验证“字符串扫描 + 早返回下标”模式。
