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

```java
class LcLongestValidParenthesesLen {
    public static int lc_longest_valid_parentheses_len(String s) {
        int[] st = new int[s.length() + 1]; int top = 0, best = 0; st[top++] = -1; for (int i = 0; i < s.length(); i++) { if (s.charAt(i) == '(') st[top++] = i; else { top--; if (top == 0) st[top++] = i; else best = Math.max(best, i - st[top - 1]); } } return best;
    }
}
```
