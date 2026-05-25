# Sum To N

## 问题描述

实现一个 Java 静态方法，输入正整数 `n`，返回 `1 + 2 + ... + n` 的结果。

约定：

- `n >= 0`
- 结果保证在 Java int 范围内
- 方法不读写额外状态

## Java 要求

- 生成的 Java 类名应为 `SumToN`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class SumToN {
    public static int sum_to_n(int n) {
        int i;
        int ret = 0;

        for (i = 1; i <= n; ++i) {
            ret += i;
        }

        return ret;
    }
}
```

## 说明

这是一道最基础的循环累加题：

- 单层循环
- 标量状态
- 没有数组
- invariant 适合写成“`ret` 等于前 `i - 1` 个正整数之和”
