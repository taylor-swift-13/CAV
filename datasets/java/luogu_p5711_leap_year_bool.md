# Luogu P5711 Leap Year Bool

## Problem

Return true if `year` is a Gregorian leap year.

## Requirements

- Use the standard rule: divisible by 400, or divisible by 4 and not by 100.

## Source

- Source: Luogu problem `P5711`.
- URL: https://www.luogu.com.cn/problem/P5711
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5711LeapYearBool {
    public static boolean luogu_p5711_leap_year_bool(int year) {
        return year % 400 == 0 || (year % 4 == 0 && year % 100 != 0);
    }
}
```
