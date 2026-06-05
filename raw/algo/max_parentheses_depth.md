# max_parentheses_depth

## Problem

Return the maximum nesting depth of parentheses in `s`.

## Requirements

- Input is a valid parentheses expression possibly containing other ASCII characters.
- Only `(` and `)` affect depth.
- Return `0` if there are no parentheses.
- Track maximum open-parenthesis count.

## Source

- Source: LeetCode problem `maximum-nesting-depth-of-the-parentheses`.
- URL: https://leetcode.com/problems/maximum-nesting-depth-of-the-parentheses/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int max_parentheses_depth(const char *s) {
    int depth = 0;
    int best = 0;
    for (int i = 0; s[i] != '\0'; i++) {
        if (s[i] == '(') { depth++; if (depth > best) best = depth; }
        else if (s[i] == ')') depth--;
    }
    return best;
}
```
