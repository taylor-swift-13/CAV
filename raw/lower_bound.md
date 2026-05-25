# Lower Bound

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的非递减整数数组 `a` 和目标值 `target`，返回第一个满足 `a[i] >= target` 的下标；如果不存在，返回 `n`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 数组 `a` 非递减
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `LowerBound`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class LowerBound {
    public static int lower_bound(int n, int[] a, int target) {
        int left = 0;
        int right = n;
        int mid;

        while (left < right) {
            mid = left + (right - left) / 2;
            if (a[mid] < target) {
                left = mid + 1;
            } else {
                right = mid;
            }
        }

        return left;
    }
}
```

## 说明

这是最简单的边界二分题，适合验证“半开区间 `[left, right)` 与前缀排除性质”。
