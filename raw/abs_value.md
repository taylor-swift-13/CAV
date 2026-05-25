# Absolute Value

## 问题描述

实现一个 Java 静态方法，输入一个整数 `x`，返回它的绝对值。

约定：

- 输入满足 `x != Integer.MIN_VALUE`
- 这样 `-x` 仍然在 Java int 范围内
- 方法不读写额外状态

## Java 要求

- 生成的 Java 类名应为 `AbsValue`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class AbsValue {
    public static int abs_value(int x) {
        if (x >= 0) {
            return x;
        } else {
            return -x;
        }
    }
}
```

## 说明

这道题比简单加法多一个符号翻转分支：

- 没有循环
- 没有数组
- 需要在规格中显式排除 `Integer.MIN_VALUE`
- 后置条件适合写成“返回值非负，且等于 `x` 或 `-x`”
