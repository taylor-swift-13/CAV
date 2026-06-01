# LC Decode Ways Count

## Problem

Return how many ways digit string `s` can be decoded with `1 -> A` through `26 -> Z`.

## Requirements

- `s` contains digits only.
- The empty string returns `0`.
- The result fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `decode-ways`.
- URL: https://leetcode.com/problems/decode-ways/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_decode_ways_count(const char *s) {
    int n = 0;
    while (s[n] != '\0') n++;
    if (n == 0) return 0;
    int dp[128] = {0};
    dp[0] = 1;
    dp[1] = s[0] == '0' ? 0 : 1;
    for (int i = 2; i <= n; i++) {
        if (s[i - 1] != '0') dp[i] += dp[i - 1];
        int two = (s[i - 2] - '0') * 10 + (s[i - 1] - '0');
        if (two >= 10 && two <= 26) dp[i] += dp[i - 2];
    }
    return dp[n];
}
```
