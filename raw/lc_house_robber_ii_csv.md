# LC House Robber II CSV

## Problem

Return the maximum amount that can be robbed from circularly arranged houses.

## Requirements

- `nums` is a nonempty comma-separated list of nonnegative integers.
- Adjacent houses in the circle cannot both be robbed.

## Source

- Source: LeetCode problem `house-robber-ii`.
- URL: https://leetcode.com/problems/house-robber-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_house_robber_ii_csv(const char *nums) {
    int a[256], n = 0, i = 0;
    while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n++] = v; if (nums[i] == ',') i++; }
    if (n == 1) return a[0];
    int prev = 0, cur = 0; for (int j = 0; j < n - 1; j++) { int next = prev + a[j] > cur ? prev + a[j] : cur; prev = cur; cur = next; } int best1 = cur;
    prev = 0; cur = 0; for (int j = 1; j < n; j++) { int next = prev + a[j] > cur ? prev + a[j] : cur; prev = cur; cur = next; }
    return best1 > cur ? best1 : cur;
}
```
