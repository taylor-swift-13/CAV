# Array Last Positive

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，返回最后一个正数元素的下标；如果不存在正数，返回 `-1`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayLastPositive`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayLastPositive {
    public static int array_last_positive(int n, int[] a) {
        int i;
        int ans = -1;

        for (i = 0; i < n; ++i) {
            if (a[i] > 0) {
                ans = i;
            }
        }

        return ans;
    }
}
```

## 说明

这道题适合验证“扫描状态量保存最后一次命中位置”模式。
