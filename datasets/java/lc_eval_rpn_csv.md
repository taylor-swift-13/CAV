# LC Evaluate RPN CSV

## Problem

Evaluate a reverse Polish notation expression encoded as comma-separated tokens.

## Requirements

- Tokens are integers or one of `+`, `-`, `*`, `/`.
- Division truncates toward zero.
- The expression is valid.

## Source

- Source: LeetCode problem `evaluate-reverse-polish-notation`.
- URL: https://leetcode.com/problems/evaluate-reverse-polish-notation/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcEvalRpnCsv {
    public static int lc_eval_rpn_csv(String tokens) {
        String[] parts = tokens.split(",");
        int[] stack = new int[parts.length];
        int top = 0;
        for (String raw : parts) { String t = raw.trim(); if (t.equals("+") || t.equals("-") || t.equals("*") || t.equals("/")) { int b = stack[--top], a = stack[--top]; if (t.equals("+")) stack[top++] = a + b; else if (t.equals("-")) stack[top++] = a - b; else if (t.equals("*")) stack[top++] = a * b; else stack[top++] = a / b; } else stack[top++] = Integer.parseInt(t); }
        return stack[0];
    }
}
```
