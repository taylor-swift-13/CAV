# String Count Char

## 问题描述

实现一个 Java 静态方法，输入字符串 `s` 和字符 `c`，返回 `s` 中字符 `c` 出现的次数。

约定：

- `s` 是合法的以 `'\0'` 结尾的字符串
- 方法不修改字符串

## Java 要求

- 生成的 Java 类名应为 `StringCountChar`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringCountChar {
    public static int string_count_char(char[] s, char c) {
        int i = 0;
        int ret = 0;

        while (s[i] != '\0') {
            if (s[i] == c) {
                ret++;
            }
            i++;
        }

        return ret;
    }
}
```

## 说明

这道题是最基础的字符串计数：

- 单层循环
- 一个分支
- 只读字符串
