# String Replace Char

## 问题描述

实现一个 Java 静态方法，输入一个以 `'\0'` 结尾的字符串 `s`，以及两个字符 `old_c` 和 `new_c`。把字符串中所有等于 `old_c` 的字符原地替换成 `new_c`。

约定：

- 字符串是合法的 C 风格字符串
- 方法原地修改字符串
- 终止符 `'\0'` 保持在原位置
- 对每个终止符前的下标 `i`，如果原来 `s[i] == old_c`，执行后 `s[i] == new_c`，否则保持原值

## Java 要求

- 生成的 Java 类名应为 `StringReplaceChar`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringReplaceChar {
    public static void string_replace_char(char[] s, char old_c, char new_c) {
        int i = 0;

        while (s[i] != '\0') {
            if (s[i] == old_c) {
                s[i] = new_c;
            }
            i++;
        }
    }
}
```

## 说明

这道题适合验证“字符串原地条件替换”的模式。
