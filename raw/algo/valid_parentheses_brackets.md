# valid_parentheses_brackets

## Problem

Return true if `s` is a valid bracket string over `()[]{}`.

## Requirements

- Input contains only bracket characters.
- Every closing bracket must match the most recent unmatched opening bracket.
- Return true for the empty string.
- Maximum tested length is below 128.

## Source

- Source: LeetCode problem `valid-parentheses`.
- URL: https://leetcode.com/problems/valid-parentheses/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int valid_parentheses_brackets(const char *s) {
    char stack[128];
    int top = 0;
    for (int i = 0; s[i] != '\0'; i++) {
        char c = s[i];
        if (c == '(' || c == '[' || c == '{') { stack[top] = c; top++; }
        else {
            if (top == 0) return 0;
            char o = stack[--top];
            if ((c == ')' && o != '(') || (c == ']' && o != '[') || (c == '}' && o != '{')) return 0;
        }
    }
    return top == 0;
}
```
