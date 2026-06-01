# LC Longest Valid Parentheses Length

## Problem

Return the length of the longest valid parentheses substring.

## Requirements

- `s` contains only `(` and `)`.

## Source

- Source: LeetCode problem `longest-valid-parentheses`.
- URL: https://leetcode.com/problems/longest-valid-parentheses/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_longest_valid_parentheses_len(const char *s) {
    int st[512], top = 0, best = 0; st[top++] = -1; for (int i = 0; s[i] != '\0'; i++) { if (s[i] == '(') st[top++] = i; else { top--; if (top == 0) st[top++] = i; else { int len = i - st[top - 1]; if (len > best) best = len; } } } return best;
}
```
