# LC Wiggle Subsequence Max Length CSV

## Problem

Return the length of the longest wiggle subsequence.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `wiggle-subsequence`.
- URL: https://leetcode.com/problems/wiggle-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_wiggle_max_length_csv(const char *nums) {
    int a[512], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }
    int up = 1, down = 1; for (int j = 1; j < n; j++) { if (a[j] > a[j - 1]) up = down + 1; else if (a[j] < a[j - 1]) down = up + 1; } return up > down ? up : down;
}
```
