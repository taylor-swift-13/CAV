# Count Multiples

## 问题描述

实现一个 Java 静态方法，输入正整数 `n` 和正整数 `k`，返回 `1..n` 中能被 `k` 整除的整数个数。

约定：

- `n >= 1`
- `k >= 1`
- 枚举所有 `1 <= i <= n` 的整数

## Java 要求

- 生成的 Java 类名应为 `CountMultiples`。
- 目标方法应为 `public static`。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class CountMultiples {
    public static int count_multiples(int n, int k) {
        int i;
        int cnt = 0;

        for (i = 1; i <= n; ++i) {
            if (i % k == 0) {
                cnt++;
            }
        }

        return cnt;
    }
}
```

## 说明

这是最简单的整除计数题，适合验证“数论条件计数”。
