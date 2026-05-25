# Max Of Three

## 问题描述

实现一个 Java 静态方法，输入三个整数 `a`、`b`、`c`，返回其中的最大值。

约定：

- 输入都是普通整数
- 返回值必须等于三个输入中的一个
- 返回值不小于任意输入

## Java 要求

- 生成的 Java 类名应为 `MaxOfThree`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class MaxOfThree {
    public static int max_of_three(int a, int b, int c) {
        int m = a;

        if (b > m) {
            m = b;
        }
        if (c > m) {
            m = c;
        }

        return m;
    }
}
```

## 说明

这是最简单的三数最大值题，适合验证“分支更新 + 最值语义”。
