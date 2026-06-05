# LC Find Duplicate Number CSV

## Problem

Return the duplicated number in comma-separated `nums`.

## Requirements

- `nums` has length `n+1` and values in `1..n`.
- At least one duplicate exists.

## Source

- Source: LeetCode problem `find-the-duplicate-number`.
- URL: https://leetcode.com/problems/find-the-duplicate-number/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_find_duplicate_number_csv(const char *nums) {
    int seen[2048] = {0}, i = 0; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } if (seen[v]) return v; seen[v] = 1; if (nums[i] == ',') i++; } return -1;
}
```
