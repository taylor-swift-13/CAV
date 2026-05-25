# Array Sign

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a` 和长度为 `n` 的输出数组 `out`。对每个元素，正数写 `1`，负数写 `-1`，零写 `0`。

约定：

- `n >= 0`
- `a` 和 `out` 的长度都恰好是 `n`
- 方法不修改 `a`

## Java 要求

- 生成的 Java 类名应为 `ArraySign`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArraySign {
    public static void array_sign(int n, int[] a, int[] out) {
        int i;

        for (i = 0; i < n; ++i) {
            if (a[i] > 0) {
                out[i] = 1;
            } else if (a[i] < 0) {
                out[i] = -1;
            } else {
                out[i] = 0;
            }
        }
    }
}
```

## 说明

这道题适合验证“数组条件分类 + 多分支输出”模式。
