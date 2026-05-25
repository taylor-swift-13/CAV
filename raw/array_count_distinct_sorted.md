# Array Count Distinct Sorted

## 问题描述

实现一个 Java 静态方法，统计有序数组中不同整数值的个数。

约定：
- `n` 表示数组长度，`n >= 0`。
- `a` 表示长度至少为 `n` 的整数数组。
- 输入数组按非降序排列。
- 如果 `n == 0`，返回 `0`。

## Java 要求

- 生成的 Java 类名应为 `ArrayCountDistinctSorted`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayCountDistinctSorted {
    public static int array_count_distinct_sorted(int n, int[] a) {
        if (n == 0) {
            return 0;
        }
        int count = 1;
        int i = 1;
        while (i < n) {
            if (a[i] != a[i - 1]) {
                count++;
            }
            i++;
        }
        return count;
    }
}
```

## 说明

有序数组中相同元素一定连续出现。因此只需要统计当前位置是否与前一个位置不同，就能得到不同值的个数。
