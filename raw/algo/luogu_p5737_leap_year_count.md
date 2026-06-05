# Luogu P5737 Leap Year Count

## Problem

Return how many leap years are in the inclusive range `[start, end]`.

## Requirements

- `start <= end`.
- Use Gregorian leap-year rules.

## Source

- Source: Luogu problem `P5737`.
- URL: https://www.luogu.com.cn/problem/P5737
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5737_leap_year_count(int start, int end) {
    int count = 0;
    for (int y = start; y <= end; y++) if (y % 400 == 0 || (y % 4 == 0 && y % 100 != 0)) count++;
    return count;
}
```
