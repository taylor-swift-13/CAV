# LC Valid Mountain Array CSV

## Problem

Return true if comma-separated array `arr` is a valid mountain array.

## Requirements

- The empty string represents an empty array.
- A valid mountain has length at least `3`, strictly increases, then strictly decreases.

## Source

- Source: LeetCode problem `valid-mountain-array`.
- URL: https://leetcode.com/problems/valid-mountain-array/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_valid_mountain_array_csv(const char *arr) {
    int a[128], n = 0, i = 0;
    if (arr[0] == '\0') return 0;
    while (arr[i] != '\0') { int sign = 1, v = 0; if (arr[i] == '-') { sign = -1; i++; } while (arr[i] >= '0' && arr[i] <= '9') { v = v * 10 + arr[i] - '0'; i++; } a[n++] = sign * v; if (arr[i] == ',') i++; }
    if (n < 3) return 0;
    int p = 0;
    while (p + 1 < n && a[p] < a[p + 1]) p++;
    if (p == 0 || p == n - 1) return 0;
    while (p + 1 < n && a[p] > a[p + 1]) p++;
    return p == n - 1;
}
```
