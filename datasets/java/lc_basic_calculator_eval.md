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

```java
class LcBasicCalculatorEval {
    public static int lc_basic_calculator_eval(String s) {
        int[] stack = new int[s.length() + 1]; int top = 0, res = 0, num = 0, sign = 1; for (int i = 0; i < s.length(); i++) { char ch = s.charAt(i); if (ch >= '0' && ch <= '9') num = num * 10 + ch - '0'; else if (ch == '+') { res += sign * num; num = 0; sign = 1; } else if (ch == '-') { res += sign * num; num = 0; sign = -1; } else if (ch == '(') { stack[top++] = res; stack[top++] = sign; res = 0; sign = 1; } else if (ch == ')') { res += sign * num; num = 0; int prevSign = stack[--top]; int prevRes = stack[--top]; res = prevRes + prevSign * res; } } return res + sign * num;
    }
}
```
