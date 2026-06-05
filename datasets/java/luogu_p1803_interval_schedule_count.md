# Luogu P1803 Interval Schedule Count

## Problem

Return the maximum number of non-overlapping intervals that can be selected.

## Requirements

- Intervals are encoded as `start,end;...`.
- Select by earliest finishing time.

## Source

- Source: Luogu problem `P1803`.
- URL: https://www.luogu.com.cn/problem/P1803
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP1803IntervalScheduleCount {
    public static int luogu_p1803_interval_schedule_count(String intervals) {
        String[] rows = intervals.split(";"); int[][] a = new int[rows.length][2]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(","); a[i][0] = Integer.parseInt(p[0]); a[i][1] = Integer.parseInt(p[1]); } java.util.Arrays.sort(a, (x, y) -> Integer.compare(x[1], y[1])); int ans = 0, end = -1; for (int[] in : a) if (in[0] >= end) { ans++; end = in[1]; } return ans;
    }
}
```
