# LC Basic Calculator II Eval

## Problem

Evaluate an arithmetic expression with `+`, `-`, `*`, and `/`.

## Requirements

- Expression contains nonnegative integers, operators, and spaces.
- Division truncates toward zero.

## Source

- Source: LeetCode problem `basic-calculator-ii`.
- URL: https://leetcode.com/problems/basic-calculator-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_basic_calculator2_eval(const char *s) {
    int stack[512], top = 0, num = 0; char op = '+'; for (int i = 0;; i++) { char ch = s[i]; if (ch >= '0' && ch <= '9') num = num * 10 + ch - '0'; if ((ch != ' ' && (ch < '0' || ch > '9')) || ch == '\0') { if (op == '+') { stack[top] = num; top++; } else if (op == '-') { stack[top] = -num; top++; } else if (op == '*') stack[top - 1] *= num; else stack[top - 1] /= num; op = ch; num = 0; } if (ch == '\0') break; } int ans = 0; for (int i = 0; i < top; i++) ans += stack[i]; return ans;
}
```
