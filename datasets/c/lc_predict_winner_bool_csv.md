# LC Predict The Winner Bool CSV

## Problem

Return true if player 1 can win or tie under optimal play.

## Requirements

- `nums` is a nonempty comma-separated list of scores.
- Each turn takes one number from either end.

## Source

- Source: LeetCode problem `predict-the-winner`.
- URL: https://leetcode.com/problems/predict-the-winner/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_predict_winner_bool_csv(const char *nums) {
    int a[256], n = 0, i = 0; while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = sign * v; if (nums[i] == ',') i++; } int dp[256]; for (int x = 0; x < n; x++) dp[x] = a[x]; for (int len = 2; len <= n; len++) for (int l = 0; l + len <= n; l++) { int r = l + len - 1; int left = a[l] - dp[l + 1], right = a[r] - dp[l]; dp[l] = left > right ? left : right; } return dp[0] >= 0;
}
```
