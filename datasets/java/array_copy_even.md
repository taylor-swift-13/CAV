# Array Copy Even

## 问题描述

实现一个函数，把输入数组中的偶数复制到输出数组同位置，奇数位置写 `0`。

约定：

- `n >= 0`。
- `a` 和 `out` 长度至少为 `n`。
- 不修改输入数组。

## 参考实现

```java
class ArrayCopyEven {
    public static void array_copy_even(int n, int[] a, int[] out) {
        int i = 0;
        while (i < n) {
            if (a[i] % 2 == 0) out[i] = a[i];
            else out[i] = 0;
            i++;
        }
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
