# pivot_index_csv

## Problem

Return the leftmost pivot index of comma-separated integer array `nums`, or `-1` if none exists.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string has no pivot and returns `-1`.
- A pivot has equal sum strictly to its left and strictly to its right.
- Return the leftmost pivot index.

## Source

- Source: LeetCode problem `find-pivot-index`.
- URL: https://leetcode.com/problems/find-pivot-index/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int pivot_index_csv(const char *nums) {
    int values[128];
    int n = 0, total = 0, i = 0;
    while (nums[i] != '\0') { int sign = 1; if (nums[i] == '-') { sign = -1; i++; } int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } values[n] = sign * v; n++; total += sign * v; if (nums[i] == ',') i++; }
    int left = 0;
    for (int j = 0; j < n; j++) { if (left == total - left - values[j]) return j; left += values[j]; }
    return -1;
}
```
