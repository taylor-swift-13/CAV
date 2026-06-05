# Luogu P5718 Minimum CSV

## Problem

Return the minimum value in a comma-separated integer list.

## Requirements

- `nums` is nonempty.
- Values fit in signed 32-bit integer range.

## Source

- Source: Luogu problem `P5718`.
- URL: https://www.luogu.com.cn/problem/P5718
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5718_min_csv(const char *nums) {
    int i = 0, first = 1, best = 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } v *= sign; if (first || v < best) { best = v; first = 0; } if (nums[i] == ',') i++; }
    return best;
}
```
