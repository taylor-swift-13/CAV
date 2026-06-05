# LC Find Peak Index CSV

## Problem

Return an index `i` such that `nums[i]` is greater than its neighbors; endpoints only need their one neighbor.

## Requirements

- `nums` is nonempty.
- Adjacent values are distinct in the supplied tests.

## Source

- Source: LeetCode problem `find-peak-element`.
- URL: https://leetcode.com/problems/find-peak-element/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_find_peak_index_csv(const char *nums) {
    int a[128], n = 0, i = 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n++] = sign * v; if (nums[i] == ',') i++; }
    int l = 0, r = n - 1;
    while (l < r) { int m = l + (r - l) / 2; if (a[m] < a[m + 1]) l = m + 1; else r = m; }
    return l;
}
```
