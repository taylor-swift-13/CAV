# LC Longest Increasing Subsequence Length CSV

## Problem

Return the length of the longest strictly increasing subsequence in comma-separated integers.

## Requirements

- `nums` is nonempty.
- The answer fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `longest-increasing-subsequence`.
- URL: https://leetcode.com/problems/longest-increasing-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_lis_length_csv(const char *nums) {
    int a[256], n = 0, i = 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = sign * v; n++; if (nums[i] == ',') i++; }
    int dp[256], best = 1; for (int x = 0; x < n; x++) { dp[x] = 1; for (int y = 0; y < x; y++) if (a[y] < a[x] && dp[y] + 1 > dp[x]) dp[x] = dp[y] + 1; if (dp[x] > best) best = dp[x]; }
    return best;
}
```
