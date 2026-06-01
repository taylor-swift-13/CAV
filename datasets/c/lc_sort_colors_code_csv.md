# LC Sort Colors Code CSV

## Problem

Sort comma-separated colors `0`, `1`, and `2`, then return the decimal code formed by the sorted colors.

## Requirements

- This scalar return is a deterministic encoding of the original sorted-array output.
- The supplied arrays have at most 9 elements.

## Source

- Source: LeetCode problem `sort-colors`.
- URL: https://leetcode.com/problems/sort-colors/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_sort_colors_code_csv(const char *colors) {
    int cnt[3] = {0}, i = 0; while (colors[i] != '\0') { cnt[colors[i] - '0']++; i++; if (colors[i] == ',') i++; } int code = 0; for (int v = 0; v < 3; v++) for (int k = 0; k < cnt[v]; k++) code = code * 10 + v; return code;
}
```
