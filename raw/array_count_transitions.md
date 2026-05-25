# Array Count Transitions

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，统计相邻元素发生变化的次数。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 方法不修改数组
- 对每个 `i >= 1`，如果 `a[i] != a[i - 1]`，则计数加一

## Java 要求

- 生成的 Java 类名应为 `ArrayCountTransitions`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayCountTransitions {
    public static int array_count_transitions(int n, int[] a) {
        int i;
        int cnt = 0;

        for (i = 1; i < n; ++i) {
            if (a[i] != a[i - 1]) {
                cnt++;
            }
        }

        return cnt;
    }
}
```

## 说明

这道题适合验证“相邻元素比较 + 条件计数”模式。
