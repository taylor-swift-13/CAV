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

```c
int lc_score_parentheses_value(const char *s) {
    int ans = 0, depth = 0; for (int i = 0; s[i] != '\0'; i++) { if (s[i] == '(') depth++; else { depth--; if (i > 0 && s[i - 1] == '(') ans += 1 << depth; } } return ans;
}
```
