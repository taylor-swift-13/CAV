# String Fill Char

## 问题描述

实现一个函数，输入整数 `n`、字符 `c` 和缓冲区 `s`。把前 `n` 个位置全部写成 `c`，最后一个位置写终止符。

约定：

- `n >= 0`
- `s` 缓冲区长度至少是 `n + 1`
- 需要原地写入字符串

## 参考实现

```rust
pub fn string_fill_char(n: i32, c: u8, s: &mut [u8]) {
    let mut i: i32;

    i = 0;
    while i < n {
        s[(i) as usize] = c;
        i += 1;
    }
    s[(n) as usize] = b'\0';
}
```

## 说明

这道题适合验证“字符缓冲区批量填充”模式。
