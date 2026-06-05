# String Count Hash

## 问题描述

实现一个函数，统计 C 风格字符串中 `#` 字符的数量。

约定：

- 输入是以 `\0` 结尾的字符串。
- 只统计 ASCII `#`。
- 空字符串返回 `0`。

## 参考实现

```c
int string_count_hash(char *s) {
    int count = 0;
    for (int i = 0; s[i] != '\0'; i++) if (s[i] == '#') count++;
    return count;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
