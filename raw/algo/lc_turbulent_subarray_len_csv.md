# LC Longest Turbulent Subarray Length CSV

## Problem

Return the length of the longest turbulent subarray.

## Requirements

- Adjacent comparisons must alternate between greater-than and less-than.

## Source

- Source: LeetCode problem `longest-turbulent-subarray`.
- URL: https://leetcode.com/problems/longest-turbulent-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_turbulent_subarray_len_csv(const char *arr) {
    int a[512], n = 0, i = 0; while (arr[i] != '\0') { int v = 0; while (arr[i] >= '0' && arr[i] <= '9') { v = v * 10 + (arr[i] - '0'); i++; } a[n] = v; n++; if (arr[i] == ',') i++; } int up = 1, down = 1, best = 1; for (int j = 1; j < n; j++) { if (a[j] > a[j - 1]) { up = down + 1; down = 1; } else if (a[j] < a[j - 1]) { down = up + 1; up = 1; } else { up = 1; down = 1; } if (up > best) best = up; if (down > best) best = down; } return best;
}
```
