# Array All Even

## 问题描述

实现一个函数，判断长度为 `n` 的整数数组是否全部为偶数。

约定：

- `n >= 0`。
- 空数组返回 `1`。
- 负偶数也视为偶数。

## 参考实现

```c
int array_all_even(int n, int *a) {
    int i = 0;
    while (i < n) {
        if (a[i] % 2 != 0) return 0;
        i++;
    }
    return 1;
}
```

## 说明

这是 internal 本地补充的基础单函数算法题。
