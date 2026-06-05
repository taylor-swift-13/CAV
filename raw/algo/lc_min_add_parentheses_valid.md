# LC Minimum Add Parentheses Valid

## Problem

Return the minimum number of parentheses insertions needed to make `s` valid.

## Requirements

- `s` contains only `(` and `)`.

## Source

- Source: LeetCode problem `minimum-add-to-make-parentheses-valid`.
- URL: https://leetcode.com/problems/minimum-add-to-make-parentheses-valid/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_min_add_parentheses_valid(const char *s) {
    int bal = 0, add = 0; for (int i = 0; s[i] != '\0'; i++) { if (s[i] == '(') bal++; else if (bal > 0) bal--; else add++; } return add + bal;
}
```
