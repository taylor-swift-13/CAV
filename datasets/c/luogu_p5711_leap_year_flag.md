# Luogu P5711 Leap Year Flag

## Problem

Return `1` when `year` is a Gregorian leap year and `0` otherwise.

## Requirements

- `year > 0`.
- Years divisible by `400` are leap years.
- Years divisible by `100` but not `400` are not leap years.
- Other years divisible by `4` are leap years.

## Source

- Source: Luogu problem `P5711`.
- URL: https://www.luogu.com.cn/problem/P5711
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5711_leap_year_flag(int year) {
    if (year % 400 == 0) return 1;
    if (year % 100 == 0) return 0;
    if (year % 4 == 0) return 1;
    return 0;
}
```
