# LC Min Stack Final Min CSV

## Problem

Simulate stack operations and return the minimum value after all operations.

## Requirements

- Operations are semicolon-separated: `push:x` or `pop`.
- The final stack is nonempty.
- Pop operations are valid.

## Source

- Source: LeetCode problem `min-stack`.
- URL: https://leetcode.com/problems/min-stack/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_min_stack_final_min_csv(const char *ops) {
    int st[128], top = 0, i = 0;
    while (ops[i] != '\0') { if (ops[i] == 'p' && ops[i + 1] == 'u') { while (ops[i] != ':') i++; i++; int sign = 1, v = 0; if (ops[i] == '-') { sign = -1; i++; } while (ops[i] >= '0' && ops[i] <= '9') { v = v * 10 + (ops[i] - '0'); i++; } st[top++] = sign * v; } else { top--; while (ops[i] != '\0' && ops[i] != ';') i++; } if (ops[i] == ';') i++; }
    int min = st[0]; for (int j = 1; j < top; j++) if (st[j] < min) min = st[j];
    return min;
}
```
