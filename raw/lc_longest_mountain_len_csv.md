# LC Longest Mountain Length CSV

## Problem

Return the length of the longest mountain subarray.

## Requirements

- A mountain strictly increases then strictly decreases and has length at least 3.

## Source

- Source: LeetCode problem `longest-mountain-in-array`.
- URL: https://leetcode.com/problems/longest-mountain-in-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_longest_mountain_len_csv(const char *arr) {
    int a[512], n = 0, i = 0; while (arr[i] != '\0') { int v = 0; while (arr[i] >= '0' && arr[i] <= '9') { v = v * 10 + (arr[i] - '0'); i++; } a[n++] = v; if (arr[i] == ',') i++; } int best = 0; for (int peak = 1; peak + 1 < n; peak++) if (a[peak - 1] < a[peak] && a[peak] > a[peak + 1]) { int l = peak, r = peak; while (l > 0 && a[l - 1] < a[l]) l--; while (r + 1 < n && a[r] > a[r + 1]) r++; int len = r - l + 1; if (len > best) best = len; } return best;
}
```
