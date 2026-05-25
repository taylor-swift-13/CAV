# String Is Empty

## 问题描述

实现一个 Java 静态方法，输入一个以 `'\0'` 结尾的字符串 `s`，判断它是否为空串。

约定：

- 如果 `s[0] == '\0'`，返回 `1`
- 否则返回 `0`
- 方法不修改字符串内容

## Java 要求

- 生成的 Java 类名应为 `StringIsEmpty`。
- 目标方法应为 `public static`。
- 原版中的字符指针按 Java `char[]` 表示，以 `'\0'` 作为字符串结束符。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class StringIsEmpty {
    public static int string_is_empty(char[] s) {
        if (s[0] == '\0') {
            return 1;
        } else {
            return 0;
        }
    }
}
```

## 说明

这是最简单的字符串判定题：

- 没有循环
- 一个分支
- 只读第一个字符
