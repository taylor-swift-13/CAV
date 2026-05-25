# String All Digits

## 问题描述

实现一个函数，判断一个以 `'\0'` 结尾的字符串是否全部由 ASCII 数字字符组成。

约定：

- 字符串是合法的 C 风格字符串
- 函数不修改字符串
- 空字符串返回 `1`
- 如果每个终止符前的字符都在 `'0'` 到 `'9'` 之间，返回 `1`
- 否则返回 `0`

## 参考实现

```rust
pub fn string_all_digits(s: &[u8]) -> i32 {
    let mut i: i32 = 0;

    while s[(i) as usize] != b'\0' {
        if s[(i) as usize] < b'0' || s[(i) as usize] > b'9' {
            return 0;
        }
        i += 1;
    }

    return 1;
}
```

## 说明

这道题适合验证“字符串扫描 + 字符范围判断 + 早返回”的模式。
