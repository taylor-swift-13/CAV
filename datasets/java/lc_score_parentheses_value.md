# LC Score Of Parentheses Value

## Problem

Return the score of a balanced parentheses string.

## Requirements

- Score rules are `()` = 1, concatenation sums, and wrapping doubles.

## Source

- Source: LeetCode problem `score-of-parentheses`.
- URL: https://leetcode.com/problems/score-of-parentheses/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcScoreParenthesesValue {
    public static int lc_score_parentheses_value(String s) {
        int ans = 0, depth = 0; for (int i = 0; i < s.length(); i++) { if (s.charAt(i) == '(') depth++; else { depth--; if (s.charAt(i - 1) == '(') ans += 1 << depth; } } return ans;
    }
}
```
