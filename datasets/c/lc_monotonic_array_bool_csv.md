# LC Monotonic Array Bool CSV

## Problem

Return true if comma-separated `nums` is monotone nondecreasing or nonincreasing.

## Requirements

- `nums` is nonempty.

## Source

- Source: LeetCode problem `monotonic-array`.
- URL: https://leetcode.com/problems/monotonic-array/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_monotonic_array_bool_csv(const char *nums) {
    int prev = 0, first = 1, inc = 1, dec = 1, i = 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; if (!first) { if (v < prev) inc = 0; if (v > prev) dec = 0; } first = 0; prev = v; if (nums[i] == ',') i++; }
    return inc || dec;
}
```
