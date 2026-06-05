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

```java
class LcPredictWinnerBoolCsv {
    public static boolean lc_predict_winner_bool_csv(String nums) {
        String[] p = nums.split(","); int n = p.length; int[] a = new int[n], dp = new int[n]; for (int i = 0; i < n; i++) { a[i] = Integer.parseInt(p[i]); dp[i] = a[i]; } for (int len = 2; len <= n; len++) for (int l = 0; l + len <= n; l++) { int r = l + len - 1; dp[l] = Math.max(a[l] - dp[l + 1], a[r] - dp[l]); } return dp[0] >= 0;
    }
}
```
