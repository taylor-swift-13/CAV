# String Count Lowercase

## 问题描述

实现一个函数，输入一个以 `'\0'` 结尾的字符串 `s`，统计其中小写英文字母的个数。

约定：

- 输入是合法的 C 风格字符串
- 小写英文字母范围是 `'a'` 到 `'z'`
- 函数不修改字符串

## 参考实现

```rust
pub fn string_count_lowercase(s: &[u8]) -> i32 {
    let mut i: i32 = 0;
    let mut cnt: i32 = 0;

    while s[(i) as usize] != b'\0' {
        if s[(i) as usize] >= b'a' && s[(i) as usize] <= b'z' {
            cnt += 1;
        }
        i += 1;
    }

    return cnt;
}
```

## 说明

这道题适合验证“字符串扫描 + 字符范围判断 + 计数”模式。
