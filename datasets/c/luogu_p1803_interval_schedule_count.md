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

```c
int luogu_p1803_interval_schedule_count(const char *intervals) {
    int a[512][2], n = 0, i = 0; while (intervals[i] != '\0') { for (int k = 0; k < 2; k++) { int v = 0; while (intervals[i] >= '0' && intervals[i] <= '9') { v = v * 10 + intervals[i] - '0'; i++; } a[n][k] = v; if (intervals[i] == ',') i++; } n++; if (intervals[i] == ';') i++; }
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y][1] < a[x][1]) { int s = a[x][0], e = a[x][1]; a[x][0] = a[y][0]; a[x][1] = a[y][1]; a[y][0] = s; a[y][1] = e; }
    int ans = 0, end = -1; for (int x = 0; x < n; x++) if (a[x][0] >= end) { ans++; end = a[x][1]; } return ans;
}
```
