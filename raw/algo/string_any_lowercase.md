# String Any Lowercase

## 问题描述

实现一个函数，判断 C 风格字符串中是否存在 ASCII 小写字母。

约定：

- 输入是以 `\0` 结尾的字符串。
- 存在 `'a'..'z'` 返回 `1`。
- 否则返回 `0`。

## 参考实现

```c
int string_any_lowercase(char *s) {
    for (int i = 0; s[i] != '\0'; i++) if (s[i] >= 'a' && s[i] <= 'z') return 1;
    return 0;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
