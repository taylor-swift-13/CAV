# Selection Sort

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，用选择排序将数组原地排成非递减顺序。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 方法原地修改数组

## Java 要求

- 生成的 Java 类名应为 `SelectionSort`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class SelectionSort {
    public static void selection_sort(int n, int[] a) {
        int i;
        int j;
        int min_idx;
        int tmp;

        for (i = 0; i < n; ++i) {
            min_idx = i;
            for (j = i + 1; j < n; ++j) {
                if (a[j] < a[min_idx]) {
                    min_idx = j;
                }
            }
            tmp = a[i];
            a[i] = a[min_idx];
            a[min_idx] = tmp;
        }
    }
}
```

## 说明

这是经典简单排序题，适合验证“已排序前缀 + 剩余区间最小值选择”。
