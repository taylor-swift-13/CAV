# String Copy

## 问题描述

实现一个 Java 静态方法，把字符串 `src` 复制到 `dst`，包括结尾的 `'\0'`。

约定：

- `src` 是合法的以 `'\0'` 结尾的字符串
- `dst` 有足够空间容纳整个字符串和结尾的 `'\0'`
- 方法读取 `src`，写入 `dst`

## Java 要求

- 生成的 Java 类名应为 `StringCopy`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringCopy {
    public static void string_copy(char[] src, char[] dst) {
        int i = 0;

        while (src[i] != '\0') {
            dst[i] = src[i];
            i++;
        }
        dst[i] = '\0';
    }
}
```

## 说明

这道题是最基础的字符串复制：

- 单层循环
- 一个字符读、一个字符写
- 循环结束后还要写入结尾的 `'\0'`
