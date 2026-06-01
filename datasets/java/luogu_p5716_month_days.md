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

```java
class LuoguP5716MonthDays {
    public static int luogu_p5716_month_days(int year, int month) {
        int[] days = {0,31,28,31,30,31,30,31,31,30,31,30,31}; boolean leap = year % 400 == 0 || (year % 4 == 0 && year % 100 != 0); return month == 2 && leap ? 29 : days[month];
    }
}
```
