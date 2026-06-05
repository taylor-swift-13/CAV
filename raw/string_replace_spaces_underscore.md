# String Replace Spaces Underscore

## 问题描述

实现一个函数，把 C 风格字符串中的空格原地替换为下划线。

约定：

- 输入是以 `\0` 结尾的可变字符串。
- 只替换 ASCII 空格 `' '`。
- 字符串长度不变。

## 参考实现

```c
void string_replace_spaces_underscore(char *s) {
    for (int i = 0; s[i] != '\0'; i++) if (s[i] == ' ') s[i] = '_';
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
