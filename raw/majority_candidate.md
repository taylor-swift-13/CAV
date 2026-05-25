# Majority Candidate

## 问题描述

实现一个 Java 静态方法，输入长度为 `n` 的整数数组 `a`，返回 Boyer-Moore 投票算法得到的候选多数元素。

约定：

- `n >= 1`
- `a` 的长度恰好是 `n`
- 题目只要求返回候选值，不要求在方法中验证它一定出现超过一半
- 方法不修改数组

## Java 要求

- 生成的 Java 类名应为 `MajorityCandidate`。
- 目标方法应为 `public static`。
- 原版中的整数指针按 Java `int[]` 表示。
- 方法只依赖参数和数组内容，不使用全局状态。

## Java 参考实现

```java
class MajorityCandidate {
    public static int majority_candidate(int n, int[] a) {
        int i;
        int candidate = a[0];
        int count = 1;

        for (i = 1; i < n; ++i) {
            if (count == 0) {
                candidate = a[i];
                count = 1;
            } else if (a[i] == candidate) {
                count++;
            } else {
                count--;
            }
        }

        return candidate;
    }
}
```

## 说明

这是经典 Boyer-Moore 投票算法，适合验证“候选值 + 抵消计数”的状态更新。
