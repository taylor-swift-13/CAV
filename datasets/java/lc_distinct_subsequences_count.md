# LC Distinct Subsequences Count

## Problem

Return how many distinct subsequences of `s` equal `t`.

## Requirements

- Inputs are ASCII.
- The supplied counts fit in signed 32-bit range.

## Source

- Source: LeetCode problem `distinct-subsequences`.
- URL: https://leetcode.com/problems/distinct-subsequences/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcDistinctSubsequencesCount {
    public static int lc_distinct_subsequences_count(String s, String t) {
        long[] dp = new long[t.length() + 1]; dp[0] = 1; for (int i = 0; i < s.length(); i++) for (int j = t.length() - 1; j >= 0; j--) if (s.charAt(i) == t.charAt(j)) dp[j + 1] += dp[j]; return (int)dp[t.length()];
    }
}
```
