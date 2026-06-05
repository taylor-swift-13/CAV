# String Count Alnum

## 问题描述

实现一个函数，统计 C 风格字符串中 ASCII 字母或数字的数量。

约定：

- 输入是以 `\0` 结尾的字符串。
- 字母包括 `'A'..'Z'` 和 `'a'..'z'`。
- 数字包括 `'0'..'9'`。

## 参考实现

```c
int string_count_alnum(char *s) {
    int i = 0;
    int count = 0;
    while (s[i] != '\0') {
        char c = s[i];
        if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')) count++;
        i++;
    }
    return count;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
