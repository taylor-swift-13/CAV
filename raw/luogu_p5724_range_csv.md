# Luogu P5724 Range CSV

## Problem

Return the difference between the maximum and minimum value in a comma-separated integer list.

## Requirements

- `nums` is nonempty.
- Values fit in signed 32-bit integer range.

## Source

- Source: Luogu problem `P5724`.
- URL: https://www.luogu.com.cn/problem/P5724
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5724_range_csv(const char *nums) {
    int i = 0, first = 1, mn = 0, mx = 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } v *= sign; if (first) { mn = mx = v; first = 0; } else { if (v < mn) mn = v; if (v > mx) mx = v; } if (nums[i] == ',') i++; }
    return mx - mn;
}
```
