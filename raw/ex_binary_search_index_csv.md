# Exercism Binary Search Index CSV

## Problem

Return the index of `target` in a sorted comma-separated array, or `-1` if absent.

## Requirements

- The empty string represents an empty array.
- Values are sorted ascending.

## Source

- Source: Exercism problem `binary-search`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/binary-search
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_binary_search_index_csv(const char *nums, int target) {
    if (nums[0] == '\0') return -1;
    int a[128], n = 0, i = 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = sign * v; n++; if (nums[i] == ',') i++; }
    int l = 0, r = n - 1;
    while (l <= r) { int m = l + (r - l) / 2; if (a[m] == target) return m; if (a[m] < target) l = m + 1; else r = m - 1; }
    return -1;
}
```
