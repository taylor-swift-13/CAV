# Array Any Zero

## 问题描述

实现一个函数，判断长度为 `n` 的整数数组中是否存在零。

约定：

- `n >= 0`。
- 存在零返回 `1`。
- 不存在零返回 `0`。

## 参考实现

```java
class ArrayAnyZero {
    public static int array_any_zero(int n, int[] a) {
        for (int i = 0; i < n; i++) if (a[i] == 0) return 1;
        return 0;
    }
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
