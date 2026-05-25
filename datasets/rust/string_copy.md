# String Copy

## 问题描述

实现一个函数，把字符串 `src` 复制到 `dst`，包括结尾的 `'\0'`。

约定：

- `src` 是合法的以 `'\0'` 结尾的字符串
- `dst` 有足够空间容纳整个字符串和结尾的 `'\0'`
- 函数读取 `src`，写入 `dst`

## 参考实现

```rust
pub fn string_copy(src: &[u8], dst: &mut [u8]) {
    let mut i: i32 = 0;

    while src[(i) as usize] != b'\0' {
        dst[(i) as usize] = src[(i) as usize];
        i += 1;
    }
    dst[(i) as usize] = b'\0';
}
```

## 说明

这道题是最基础的字符串复制：

- 单层循环
- 一个字符读、一个字符写
- 循环结束后还要写入结尾的 `'\0'`
