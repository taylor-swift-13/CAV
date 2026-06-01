# Luogu P5707 Latest Departure

## Problem

Return the latest departure time, in minutes after midnight, to arrive by 08:00 after walking and a 10-minute buffer.

## Requirements

- `distance > 0` and `speed > 0`.
- Walking time is `ceil(distance / speed)` minutes.
- Add a fixed 10-minute buffer before arrival.
- If the departure time is before midnight, wrap to the previous day.

## Source

- Source: Luogu problem `P5707`.
- URL: https://www.luogu.com.cn/problem/P5707
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5707LatestDeparture {
    public static int luogu_p5707_latest_departure(int distance, int speed) {
        int travel = (distance + speed - 1) / speed + 10;
        int depart = 8 * 60 - travel;
        while (depart < 0) depart += 24 * 60;
        return depart;
    }
}
```
