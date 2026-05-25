# String Is Palindrome

## 问题描述

实现一个函数，判断给定长度的字符数组是否是回文。

约定：
- `n` 表示要检查的字符个数，`n >= 0`。
- `s` 指向长度至少为 `n` 的字符数组。
- 只检查前 `n` 个字符，不依赖 `'\0'` 结尾。
- 如果前 `n` 个字符正读和反读相同，返回 `1`，否则返回 `0`。

## 参考实现

```rust
pub fn string_is_palindrome(n: i32, s: &[u8]) -> i32 {
    let mut left: i32 = 0;
    let mut right: i32 = n - 1;
    while left < right {
        if s[(left) as usize] != s[(right) as usize] {
            return 0;
        }
        left += 1;
        right -= 1;
    }
    return 1;
}
```

## 说明

这段代码用双指针从两端向中间比较字符。只要出现一对不同字符，就可以确定不是回文。
