# LC Word Break Bool

## Problem

Return true if `s` can be segmented into dictionary words.

## Requirements

- Dictionary words are semicolon-separated.
- All strings are lowercase ASCII in the supplied tests.

## Source

- Source: LeetCode problem `word-break`.
- URL: https://leetcode.com/problems/word-break/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_word_break_bool(const char *s, const char *dict) {
    char w[64][32]; int wl[64], wn = 0, i = 0;
    while (dict[i] != '\0') { int j = 0; while (dict[i] != '\0' && dict[i] != ';') w[wn][j++] = dict[i++]; w[wn][j] = '\0'; wl[wn++] = j; if (dict[i] == ';') i++; }
    int n = 0; while (s[n] != '\0') n++; int dp[128] = {0}; dp[0] = 1;
    for (int pos = 0; pos < n; pos++) if (dp[pos]) for (int k = 0; k < wn; k++) { int ok = pos + wl[k] <= n; for (int j = 0; ok && j < wl[k]; j++) if (s[pos + j] != w[k][j]) ok = 0; if (ok) dp[pos + wl[k]] = 1; }
    return dp[n];
}
```
