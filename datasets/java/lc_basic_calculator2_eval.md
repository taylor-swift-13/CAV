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

```java
class LcBasicCalculator2Eval {
    public static int lc_basic_calculator2_eval(String s) {
        int[] stack = new int[s.length() + 1]; int top = 0, num = 0; char op = '+'; for (int i = 0; i <= s.length(); i++) { char ch = i == s.length() ? '\0' : s.charAt(i); if (ch >= '0' && ch <= '9') num = num * 10 + ch - '0'; if ((ch != ' ' && (ch < '0' || ch > '9')) || ch == '\0') { if (op == '+') stack[top++] = num; else if (op == '-') stack[top++] = -num; else if (op == '*') stack[top - 1] *= num; else stack[top - 1] /= num; op = ch; num = 0; } } int ans = 0; for (int i = 0; i < top; i++) ans += stack[i]; return ans;
    }
}
```
