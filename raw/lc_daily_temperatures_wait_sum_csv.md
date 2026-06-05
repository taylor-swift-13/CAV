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

```c
int lc_daily_temperatures_wait_sum_csv(const char *temps) {
    int a[256], n = 0, i = 0;
    while (temps[i] != '\0') { int v = 0; while (temps[i] >= '0' && temps[i] <= '9') { v = v * 10 + (temps[i] - '0'); i++; } a[n++] = v; if (temps[i] == ',') i++; }
    int st[256], top = 0, sum = 0;
    for (int d = 0; d < n; d++) { while (top > 0 && a[d] > a[st[top - 1]]) { int prev = st[--top]; sum += d - prev; } st[top++] = d; }
    return sum;
}
```
