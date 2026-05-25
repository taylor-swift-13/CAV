# String Reverse Copy

## 问题描述

实现一个函数，输入一个长度为 `n` 的字符串 `src` 和一个长度为 `n + 1` 的输出缓冲区 `dst`，把 `src` 逆序复制到 `dst`，并补上终止符。

约定：

- `src` 是合法的 C 风格字符串
- `dst` 缓冲区长度足够
- 函数不修改 `src`
- 执行后 `dst` 也是合法的 C 风格字符串

## 参考实现

```rust
pub fn string_reverse_copy(n: i32, src: &[u8], dst: &mut [u8]) {
    let mut i: i32;

    i = 0;
    while i < n {
        dst[(i) as usize] = src[(n - 1 - i) as usize];
        i += 1;
    }
    dst[(n) as usize] = b'\0';
}
```

## 说明

这道题适合验证“只读输入字符串 + 顺序写输出缓冲区”模式。
