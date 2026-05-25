# Array Reverse In Place

## 问题描述

实现一个 Java 静态方法，原地反转一个整数数组。

约定：
- `n` 表示数组长度，`n >= 0`。
- `a` 表示长度至少为 `n` 的整数数组。
- 方法不分配新数组，只通过交换元素修改 `a`。
- 返回后，`a[i]` 等于原数组中的 `a[n - 1 - i]`。

## Java 要求

- 生成的 Java 类名应为 `ArrayReverseInPlace`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayReverseInPlace {
    public static void array_reverse_in_place(int n, int[] a) {
        int left = 0;
        int right = n - 1;
        while (left < right) {
            int tmp = a[left];
            a[left] = a[right];
            a[right] = tmp;
            left++;
            right--;
        }
    }
}
```

## 说明

这段代码使用双指针从数组两端向中间移动。每一轮交换一对对称位置的元素，因此循环结束后整个数组被原地反转。
