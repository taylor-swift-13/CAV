# String Equal

## 问题描述

实现一个函数，输入两个以 `'\0'` 结尾的字符串 `a` 和 `b`，判断它们是否相等。

约定：

- 两个输入都是合法的 C 风格字符串
- 函数不修改字符串
- 如果两个字符串长度相同且每个位置字符都相同，返回 `1`
- 否则返回 `0`

## 参考实现

```rust
pub fn string_equal(a: &[u8], b: &[u8]) -> i32 {
    let mut i: i32 = 0;

    while a[(i) as usize] != b'\0' && b[(i) as usize] != b'\0' {
        if a[(i) as usize] != b[(i) as usize] {
            return 0;
        }
        i += 1;
    }

    if a[(i) as usize] == b'\0' && b[(i) as usize] == b'\0' {
        return 1;
    }
    return 0;
}
```

## 说明

这道题适合验证“双字符串同步扫描”模式：

- 两个输入字符串
- 循环内逐字符比较
- 循环退出后还要判断是否同时到达 terminator
