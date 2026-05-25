# Array Sum Abs

## 问题描述

实现一个函数，返回长度为 `n` 的整数数组中所有元素绝对值之和。

约定：

- `n >= 0`。
- 结果保证在 32 位有符号整数范围内。
- 不修改输入数组。

## 参考实现

```java
class ArraySumAbs {
    public static int array_sum_abs(int n, int[] a) {
        int i = 0;
        int sum = 0;
        while (i < n) {
            int v = a[i];
            if (v < 0) v = -v;
            sum += v;
            i++;
        }
        return sum;
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
