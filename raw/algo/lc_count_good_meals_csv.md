# LC Count Good Meals CSV

## Problem

Return the number of pairs whose sum is a power of two.

## Requirements

- `deliciousness` is a comma-separated list of nonnegative integers.
- The supplied counts fit in signed 32-bit range.

## Source

- Source: LeetCode problem `count-good-meals`.
- URL: https://leetcode.com/problems/count-good-meals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_count_good_meals_csv(const char *deliciousness) {
    int a[512], n = 0, i = 0; while (deliciousness[i] != '\0') { int v = 0; while (deliciousness[i] >= '0' && deliciousness[i] <= '9') { v = v * 10 + (deliciousness[i] - '0'); i++; } a[n] = v; n++; if (deliciousness[i] == ',') i++; } int ans = 0; for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) { int s = a[x] + a[y]; if (s > 0 && (s & (s - 1)) == 0) ans++; } return ans;
}
```
