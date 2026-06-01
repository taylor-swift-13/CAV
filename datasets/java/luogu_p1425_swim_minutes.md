# Luogu P1425 Swim Minutes

## Problem

Given a start time and an end time on the same day, return the elapsed number of minutes.

## Requirements

- `0 <= start_hour, end_hour < 24`.
- `0 <= start_minute, end_minute < 60`.
- The end time is not earlier than the start time.

## Source

- Source: Luogu problem `P1425`.
- URL: https://www.luogu.com.cn/problem/P1425
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP1425SwimMinutes {
    public static int luogu_p1425_swim_minutes(int start_hour, int start_minute, int end_hour, int end_minute) {
        return end_hour * 60 + end_minute - start_hour * 60 - start_minute;
    }
}
```
