# String All Uppercase

## 问题描述

实现一个函数，判断 C 风格字符串是否全部由 ASCII 大写字母组成。

约定：

- 输入是以 `\0` 结尾的字符串。
- 空字符串返回 `1`。
- 非大写字母字符会导致返回 `0`。

## 参考实现

```c
int string_all_uppercase(char *s) {
    for (int i = 0; s[i] != '\0'; i++) if (s[i] < 'A' || s[i] > 'Z') return 0;
    return 1;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
