# LC Sum Of Subarray Minimums CSV

## Problem

Return the sum of the minimum value of every contiguous subarray.

## Requirements

- `arr` is a comma-separated list of positive integers.
- The supplied sums fit in signed 32-bit range.

## Source

- Source: LeetCode problem `sum-of-subarray-minimums`.
- URL: https://leetcode.com/problems/sum-of-subarray-minimums/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_sum_subarray_mins_csv(const char *arr) {
    int a[512], n = 0, i = 0; while (arr[i] != '\0') { int v = 0; while (arr[i] >= '0' && arr[i] <= '9') { v = v * 10 + arr[i] - '0'; i++; } a[n++] = v; if (arr[i] == ',') i++; } int sum = 0; for (int l = 0; l < n; l++) { int mn = a[l]; for (int r = l; r < n; r++) { if (a[r] < mn) mn = a[r]; sum += mn; } } return sum;
}
```
