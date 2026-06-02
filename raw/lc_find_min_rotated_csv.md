# LC Find Minimum In Rotated Sorted Array CSV

## Problem

Return the minimum value in a rotated sorted array with distinct integers.

## Requirements

- `nums` is a nonempty comma-separated list.
- Values are distinct.

## Source

- Source: LeetCode problem `find-minimum-in-rotated-sorted-array`.
- URL: https://leetcode.com/problems/find-minimum-in-rotated-sorted-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_find_min_rotated_csv(const char *nums) {
    int a[256], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }
    int l = 0, r = n - 1; while (l < r) { int m = l + (r - l) / 2; if (a[m] > a[r]) l = m + 1; else r = m; } return a[l];
}
```
