# LC Teemo Attacking Duration CSV

## Problem

Return total poisoned duration from attack times and a fixed duration.

## Requirements

- `times` is a nonempty sorted comma-separated list of attack times.
- `duration > 0`.

## Source

- Source: LeetCode problem `teemo-attacking`.
- URL: https://leetcode.com/problems/teemo-attacking/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_teemo_attacking_duration_csv(const char *times, int duration) {
    int prev = -1000000000, ans = 0, i = 0; while (times[i] != '\0') { int v = 0; while (times[i] >= '0' && times[i] <= '9') { v = v * 10 + times[i] - '0'; i++; } if (prev < 0) ans += duration; else ans += v - prev < duration ? v - prev : duration; prev = v; if (times[i] == ',') i++; } return ans;
}
```
