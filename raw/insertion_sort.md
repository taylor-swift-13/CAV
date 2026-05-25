# Insertion Sort

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，用插入排序将数组原地排成非递减顺序。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 方法原地修改数组

## Java 要求

- 生成的 Java 类名应为 `InsertionSort`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class InsertionSort {
    public static void insertion_sort(int n, int[] a) {
        int i;
        int j;
        int key;

        for (i = 1; i < n; ++i) {
            key = a[i];
            j = i - 1;
            while (j >= 0 && a[j] > key) {
                a[j + 1] = a[j];
                j--;
            }
            a[j + 1] = key;
        }
    }
}
```

## 说明

这是经典插入排序题，适合验证“有序前缀 + 元素右移 + 插入位置”。
