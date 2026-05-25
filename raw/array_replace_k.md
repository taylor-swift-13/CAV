# Array Replace K

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`、整数 `old_k` 和 `new_k`，把数组中所有等于 `old_k` 的元素替换成 `new_k`。

约定：

- `n >= 0`
- 数组长度恰好是 `n`
- 需要原地修改数组

## Java 要求

- 生成的 Java 类名应为 `ArrayReplaceK`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayReplaceK {
    public static void array_replace_k(int n, int[] a, int old_k, int new_k) {
        int i;

        for (i = 0; i < n; ++i) {
            if (a[i] == old_k) {
                a[i] = new_k;
            }
        }
    }
}
```

## 说明

这道题适合验证“条件式原地更新”模式：

- 不是每轮都写
- 更新逻辑取决于当前元素是否命中
