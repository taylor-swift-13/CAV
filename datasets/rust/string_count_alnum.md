# String Count Alnum

## 问题描述

实现一个函数，统计 C 风格字符串中 ASCII 字母或数字的数量。

约定：

- 输入是以 `\0` 结尾的字符串。
- 字母包括 `'A'..'Z'` 和 `'a'..'z'`。
- 数字包括 `'0'..'9'`。

## 参考实现

```rust
pub fn string_count_alnum(s: &[u8]) -> i32 {
    let mut i = 0;
    let mut count = 0;
    while s[i as usize] != b'\0' {
        let c = s[i as usize];
        if (c >= b'A' && c <= b'Z') || (c >= b'a' && c <= b'z') || (c >= b'0' && c <= b'9') { count += 1; }
        i += 1;
    }
    count
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
