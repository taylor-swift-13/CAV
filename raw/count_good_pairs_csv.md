# count_good_pairs_csv

## Problem

Return the number of index pairs `(i,j)` with `i < j` and equal values in comma-separated integer array `nums`.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Count pairs of distinct indices with equal values.
- Return the pair count, not the values.

## Source

- Source: LeetCode problem `number-of-good-pairs`.
- URL: https://leetcode.com/problems/number-of-good-pairs/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int count_good_pairs_csv(const char *nums) {
    int values[128];
    int n = 0, i = 0;
    while (nums[i] != '\0') { int sign = 1; if (nums[i] == '-') { sign = -1; i++; } int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } values[n++] = sign * v; if (nums[i] == ',') i++; }
    int count = 0;
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (values[a] == values[b]) count++;
    return count;
}
```
