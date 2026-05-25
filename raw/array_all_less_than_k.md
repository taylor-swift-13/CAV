# Array All Less Than K

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a` 和整数 `k`，判断所有元素是否都严格小于 `k`。如果是返回 `1`，否则返回 `0`。

约定：

- `n >= 0`
- `a` 的长度恰好是 `n`
- 空数组视为满足条件
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayAllLessThanK`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayAllLessThanK {
    public static int array_all_less_than_k(int n, int[] a, int k) {
        int i;

        for (i = 0; i < n; ++i) {
            if (a[i] >= k) {
                return 0;
            }
        }

        return 1;
    }
}
```

## 说明

这道题适合验证“数组全称性质 + 反例提前返回”模式。
