# Array Count Between

## 问题描述

实现一个函数，统计长度为 `n` 的整数数组中位于闭区间 `[lo, hi]` 内的元素个数。

约定：

- `n >= 0`。
- `lo <= hi`。
- 数组长度至少为 `n`。

## 参考实现

```java
class ArrayCountBetween {
    public static int array_count_between(int n, int[] a, int lo, int hi) {
        int i = 0;
        int count = 0;
        while (i < n) {
            if (a[i] >= lo && a[i] <= hi) count++;
            i++;
        }
        return count;
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
