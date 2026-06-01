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

```java
class LcWordBreakBool {
    public static boolean lc_word_break_bool(String s, String dict) {
        String[] words = dict.split(";"); boolean[] dp = new boolean[s.length() + 1]; dp[0] = true;
        for (int i = 0; i < s.length(); i++) if (dp[i]) for (String w : words) if (i + w.length() <= s.length() && s.startsWith(w, i)) dp[i + w.length()] = true;
        return dp[s.length()];
    }
}
```
