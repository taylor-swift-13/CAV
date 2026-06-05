# Luogu P5716 Month Days

## Problem

Return the number of days in `month` for Gregorian `year`.

## Requirements

- `1 <= month <= 12`.
- Use standard leap-year rules.

## Source

- Source: Luogu problem `P5716`.
- URL: https://www.luogu.com.cn/problem/P5716
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5716_month_days(int year, int month) {
    int days[13] = {0,31,28,31,30,31,30,31,31,30,31,30,31};
    int leap = (year % 400 == 0) || (year % 4 == 0 && year % 100 != 0);
    if (month == 2 && leap) return 29;
    return days[month];
}
```
