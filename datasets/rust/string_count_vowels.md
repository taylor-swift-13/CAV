# String Count Vowels

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`，统计其中元音字母 `a e i o u` 的出现次数。

约定：

- 输入是合法的 C 风格字符串
- 函数不修改字符串

## 参考实现

```rust
pub fn string_count_vowels(s: &[u8]) -> i32 {
    let mut i: i32 = 0;
    let mut cnt: i32 = 0;

    while s[(i) as usize] != b'\0' {
        if s[(i) as usize] == b'a' || s[(i) as usize] == b'e' || s[(i) as usize] == b'i' || s[(i) as usize] == b'o' || s[(i) as usize] == b'u' {
            cnt += 1;
        }
        i += 1;
    }

    return cnt;
}
```

## 说明

这道题适合验证“字符串扫描 + 多分支命中条件”模式。
