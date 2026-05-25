# String Find Last Char

## 问题描述

实现一个函数，返回字符 `c` 在 C 风格字符串中最后一次出现的位置，不存在则返回 `-1`。

约定：

- 输入是以 `\0` 结尾的字符串。
- 返回从 `0` 开始的下标。
- 空字符串返回 `-1`。

## 参考实现

```java
class StringFindLastChar {
    public static int string_find_last_char(char[] s, char c) {
        int i = 0;
        int last = -1;
        while (s[i] != '\0') {
            if (s[i] == c) last = i;
            i++;
        }
        return last;
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
