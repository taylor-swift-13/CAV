# Array Count Increasing Steps

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，统计满足 `a[i] < a[i + 1]` 的下标个数。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayCountIncreasingSteps`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayCountIncreasingSteps {
    public static int array_count_increasing_steps(int n, int[] a) {
        int i;
        int cnt = 0;

        for (i = 0; i + 1 < n; ++i) {
            if (a[i] < a[i + 1]) {
                cnt++;
            }
        }

        return cnt;
    }
}
```

## 说明

这道题适合验证“相邻比较 + 条件计数”模式。
