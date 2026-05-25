# String Copy Prefix

## 问题描述

实现一个函数，输入长度为 `n` 的字符串 `src`、整数 `k` 和输出缓冲区 `dst`。把 `src` 的前 `k` 个字符复制到 `dst`，然后补一个终止符。

约定：

- `0 <= k <= n`
- `src` 是长度为 `n` 的合法 C 风格字符串
- `dst` 缓冲区长度至少是 `k + 1`
- 函数不修改 `src`

## 参考实现

```rust
pub fn string_copy_prefix(k: i32, src: &[u8], dst: &mut [u8]) {
    let mut i: i32;

    i = 0;
    while i < k {
        dst[(i) as usize] = src[(i) as usize];
        i += 1;
    }
    dst[(k) as usize] = b'\0';
}
```

## 说明

这道题适合验证“固定前缀复制 + 末尾补终止符”模式。
