# LC Best Sightseeing Pair Score CSV

## Problem

Return the maximum score `values[i] + values[j] + i - j` for `i < j`.

## Requirements

- `values` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `best-sightseeing-pair`.
- URL: https://leetcode.com/problems/best-sightseeing-pair/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_best_sightseeing_pair_score_csv(const char *values) {
    int a[512], n = 0, i = 0; while (values[i] != '\0') { int v = 0; while (values[i] >= '0' && values[i] <= '9') { v = v * 10 + values[i] - '0'; i++; } a[n++] = v; if (values[i] == ',') i++; } int best_left = a[0], ans = -2147483647; for (int j = 1; j < n; j++) { int score = best_left + a[j] - j; if (score > ans) ans = score; int cand = a[j] + j; if (cand > best_left) best_left = cand; } return ans;
}
```
