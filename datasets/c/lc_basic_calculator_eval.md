# LC Basic Calculator Eval

## Problem

Evaluate an arithmetic expression with `+`, `-`, parentheses, and spaces.

## Requirements

- Expression contains nonnegative integers, plus/minus signs, parentheses, and spaces.

## Source

- Source: LeetCode problem `basic-calculator`.
- URL: https://leetcode.com/problems/basic-calculator/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_basic_calculator_eval(const char *s) {
    int stack[512], top = 0, res = 0, num = 0, sign = 1; for (int i = 0; s[i] != '\0'; i++) { char ch = s[i]; if (ch >= '0' && ch <= '9') num = num * 10 + ch - '0'; else if (ch == '+') { res += sign * num; num = 0; sign = 1; } else if (ch == '-') { res += sign * num; num = 0; sign = -1; } else if (ch == '(') { stack[top++] = res; stack[top++] = sign; res = 0; sign = 1; } else if (ch == ')') { res += sign * num; num = 0; int prev_sign = stack[--top]; int prev_res = stack[--top]; res = prev_res + prev_sign * res; } } return res + sign * num;
}
```
