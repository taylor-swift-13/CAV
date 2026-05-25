# Is Multiple

## 问题描述

实现一个 Java 静态方法，输入整数 `a` 和正整数 `b`，判断 `a` 是否是 `b` 的倍数。如果是返回 `1`，否则返回 `0`。

约定：

- `b > 0`
- 返回值只使用 `0` 或 `1`

## Java 要求

- 生成的 Java 类名应为 `IsMultiple`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class IsMultiple {
    public static int is_multiple(int a, int b) {
        if (a % b == 0) {
            return 1;
        }
        return 0;
    }
}
```

## 说明

这是最简单的整除判断题，适合验证“模运算 + 布尔返回”。
