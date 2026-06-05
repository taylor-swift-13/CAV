# LC Fruit Into Baskets Length CSV

## Problem

Return the longest contiguous subarray containing at most two distinct fruit types.

## Requirements

- `fruits` is a comma-separated list of integer fruit types.

## Source

- Source: LeetCode problem `fruit-into-baskets`.
- URL: https://leetcode.com/problems/fruit-into-baskets/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_fruit_into_baskets_len_csv(const char *fruits) {
    int a[512], n = 0, i = 0; while (fruits[i] != '\0') { int v = 0; while (fruits[i] >= '0' && fruits[i] <= '9') { v = v * 10 + (fruits[i] - '0'); i++; } a[n] = v; n++; if (fruits[i] == ',') i++; } int best = 0; for (int l = 0; l < n; l++) { int t1 = -1, t2 = -1; for (int r = l; r < n; r++) { if (a[r] == t1 || a[r] == t2) { } else if (t1 == -1) t1 = a[r]; else if (t2 == -1) t2 = a[r]; else break; int len = r - l + 1; if (len > best) best = len; } } return best;
}
```
