# String All Lowercase

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`，判断其中所有字符是否都在 `'a'` 到 `'z'` 之间。

约定：

- 输入是合法的 C 风格字符串
- 函数不修改字符串
- 如果所有字符都是小写字母，返回 `1`
- 否则返回 `0`

## 参考实现

```rust
pub fn string_all_lowercase(s: &[u8]) -> i32 {
    let mut i: i32 = 0;

    while s[(i) as usize] != b'\0' {
        if s[(i) as usize] < b'a' || s[(i) as usize] > b'z' {
            return 0;
        }
        i += 1;
    }

    return 1;
}
```

## 说明

这道题适合验证“字符串扫描 + 区间判断”模式。
