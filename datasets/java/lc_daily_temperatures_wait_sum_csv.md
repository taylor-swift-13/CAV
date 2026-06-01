# LC Daily Temperatures Wait Sum CSV

## Problem

Compute daily-temperature waiting days and return their sum.

## Requirements

- `temps` is a nonempty comma-separated list of integers.
- For days with no warmer future day, the wait is `0`.

## Source

- Source: LeetCode problem `daily-temperatures`.
- URL: https://leetcode.com/problems/daily-temperatures/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcDailyTemperaturesWaitSumCsv {
    public static int lc_daily_temperatures_wait_sum_csv(String temps) {
        String[] p = temps.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int[] st = new int[a.length]; int top = 0, sum = 0;
        for (int d = 0; d < a.length; d++) { while (top > 0 && a[d] > a[st[top - 1]]) { int prev = st[--top]; sum += d - prev; } st[top++] = d; }
        return sum;
    }
}
```
