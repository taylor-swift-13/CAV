# String All Lowercase

## 问题描述

实现一个 Java 静态方法，输入一个以 `'\0'` 结尾的字符串 `s`，判断其中所有字符是否都在 `'a'` 到 `'z'` 之间。

约定：

- 输入是合法的 C 风格字符串
- 方法不修改字符串
- 如果所有字符都是小写字母，返回 `1`
- 否则返回 `0`

## Java 要求

- 生成的 Java 类名应为 `StringAllLowercase`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringAllLowercase {
    public static int string_all_lowercase(char[] s) {
        int i = 0;

        while (s[i] != '\0') {
            if (s[i] < 'a' || s[i] > 'z') {
                return 0;
            }
            i++;
        }

        return 1;
    }
}
```

## 说明

这道题适合验证“字符串扫描 + 区间判断”模式。
