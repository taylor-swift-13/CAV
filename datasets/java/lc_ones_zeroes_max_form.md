# LC Ones And Zeroes Max Form

## Problem

Return the largest subset size with at most `m` zeroes and `n` ones.

## Requirements

- Binary strings are separated by semicolons.

## Source

- Source: LeetCode problem `ones-and-zeroes`.
- URL: https://leetcode.com/problems/ones-and-zeroes/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcOnesZeroesMaxForm {
    public static int lc_ones_zeroes_max_form(String strs, int m, int n) {
        int[][] dp = new int[m + 1][n + 1]; for (String s : strs.split(";")) { int z = 0, o = 0; for (int i = 0; i < s.length(); i++) if (s.charAt(i) == '0') z++; else o++; for (int a = m; a >= z; a--) for (int b = n; b >= o; b--) dp[a][b] = Math.max(dp[a][b], dp[a - z][b - o] + 1); } return dp[m][n];
    }
}
```
