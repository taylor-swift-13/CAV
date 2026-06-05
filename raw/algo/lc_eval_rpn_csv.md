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

```c
int lc_eval_rpn_csv(const char *tokens) {
    int stack[128], top = 0, i = 0;
    while (tokens[i] != '\0') { while (tokens[i] == ' ') i++; if ((tokens[i] == '+' || tokens[i] == '*' || tokens[i] == '/') && (tokens[i + 1] == ',' || tokens[i + 1] == '\0' || tokens[i + 1] == ' ')) { int b = stack[--top], a = stack[--top]; char op = tokens[i++]; stack[top] = op == '+' ? a + b : (op == '*' ? a * b : a / b); top++; } else if (tokens[i] == '-' && (tokens[i + 1] == ',' || tokens[i + 1] == '\0' || tokens[i + 1] == ' ')) { int b = stack[--top], a = stack[--top]; i++; stack[top] = a - b; top++; } else { int sign = 1, v = 0; if (tokens[i] == '-') { sign = -1; i++; } while (tokens[i] >= '0' && tokens[i] <= '9') { v = v * 10 + (tokens[i] - '0'); i++; } stack[top] = sign * v; top++; } while (tokens[i] == ' ') i++; if (tokens[i] == ',') i++; }
    return stack[0];
}
```
