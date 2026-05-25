# String Length

## 问题描述

实现一个 Java 静态方法，输入一个以 `'\0'` 结尾的字符串 `s`，返回它的长度。

约定：

- `s` 表示合法的以 `'\0'` 结尾的字符数组
- 方法不修改字符串内容
- 返回值不包括结尾的 `'\0'`

## Java 要求

- 生成的 Java 类名应为 `StringLength`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringLength {
    public static int string_length(char[] s) {
        int i = 0;

        while (s[i] != '\0') {
            i++;
        }

        return i;
    }
}
```

## 说明

这是最基础的字符串扫描题：

- 单层循环
- 只读字符串
- 退出条件由 `'\0'` 决定
