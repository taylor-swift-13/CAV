# String Count Uppercase

## 问题描述

实现一个函数，统计 C 风格字符串中 ASCII 大写字母的数量。

约定：

- 输入是以 `\0` 结尾的字符串。
- 只统计 `'A'` 到 `'Z'`。
- 空字符串返回 `0`。

## 参考实现

```java
class StringCountUppercase {
    public static int string_count_uppercase(char[] s) {
        int i = 0;
        int count = 0;
        while (s[i] != '\0') {
            if (s[i] >= 'A' && s[i] <= 'Z') count++;
            i++;
        }
        return count;
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
