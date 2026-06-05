# Luogu P1423 Swim Days

## Problem

Return the first day on which cumulative swimming distance reaches the target distance.

## Requirements

- `x_times_100` encodes the Luogu decimal distance as `x * 100`.
- The first day distance is `2.0`; each next day is `98%` of the previous day.

## Source

- Source: Luogu problem `P1423`.
- URL: https://www.luogu.com.cn/problem/P1423
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p1423_swim_days(int x_times_100) {
    double x = x_times_100 / 100.0; double sum = 0.0, day_distance = 2.0; int days = 0; while (sum < x) { sum += day_distance; day_distance *= 0.98; days++; } return days;
}
```
