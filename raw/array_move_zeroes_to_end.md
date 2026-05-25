# Array Move Zeroes To End

## 问题描述

实现一个 Java 静态方法，把数组中的所有非零元素保持相对顺序移动到前面，并把剩余位置填成 `0`。

约定：
- `n` 表示数组长度，`n >= 0`。
- `a` 表示长度至少为 `n` 的整数数组。
- 非零元素的相对顺序必须保持不变。
- 返回后，数组前缀是原数组中按原顺序出现的所有非零元素，后缀全是 `0`。

## Java 要求

- 生成的 Java 类名应为 `ArrayMoveZeroesToEnd`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class ArrayMoveZeroesToEnd {
    public static void array_move_zeroes_to_end(int n, int[] a) {
        int write = 0;
        int i = 0;
        while (i < n) {
            if (a[i] != 0) {
                a[write] = a[i];
                write++;
            }
            i++;
        }
        while (write < n) {
            a[write] = 0;
            write++;
        }
    }
}
```

## 说明

第一轮循环把所有非零元素依次写入数组前缀。第二轮循环把剩余位置全部补成 `0`。
