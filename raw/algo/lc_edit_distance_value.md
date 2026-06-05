# LC Edit Distance Value

## Problem

Return the minimum number of insertions, deletions, and substitutions needed to transform `word1` into `word2`.

## Requirements

- Strings are ASCII.
- Both string lengths are at most `32`.
- Each edit has cost `1`.

## Source

- Source: LeetCode problem `edit-distance`.
- URL: https://leetcode.com/problems/edit-distance/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_edit_distance_value(const char *word1, const char *word2) {
    int n = 0, m = 0;
    while (word1[n] != '\0') n++;
    while (word2[m] != '\0') m++;
    int dp[33][33];
    for (int i = 0; i <= n; i++) dp[i][0] = i;
    for (int j = 0; j <= m; j++) dp[0][j] = j;
    for (int i = 1; i <= n; i++) {
        for (int j = 1; j <= m; j++) {
            int cost = word1[i - 1] == word2[j - 1] ? 0 : 1;
            int best = dp[i - 1][j] + 1;
            if (dp[i][j - 1] + 1 < best) best = dp[i][j - 1] + 1;
            if (dp[i - 1][j - 1] + cost < best) best = dp[i - 1][j - 1] + cost;
            dp[i][j] = best;
        }
    }
    return dp[n][m];
}
```
