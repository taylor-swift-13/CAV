# String Count Punctuation

## 问题描述

实现一个函数，统计 C 风格字符串中 `.`, `,`, `!`, `?` 四种标点数量。

约定：

- 输入是以 `\0` 结尾的字符串。
- 只统计四种指定 ASCII 标点。
- 空字符串返回 `0`。

## 参考实现

```java
class StringCountPunctuation {
    public static int string_count_punctuation(char[] s) {
        int count = 0;
        for (int i = 0; s[i] != '\0'; i++) if (s[i] == '.' || s[i] == ',' || s[i] == '!' || s[i] == '?') count++;
        return count;
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
