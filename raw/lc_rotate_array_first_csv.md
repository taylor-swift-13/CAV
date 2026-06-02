# LC Rotate Array First CSV

## Problem

Rotate comma-separated `nums` to the right by `k` steps and return the first element after rotation.

## Requirements

- `nums` is nonempty.
- `k >= 0`.

## Source

- Source: LeetCode problem `rotate-array`.
- URL: https://leetcode.com/problems/rotate-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_rotate_array_first_csv(const char *nums, int k) {
    int a[256], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; } k %= n; return a[(n - k) % n];
}
```
