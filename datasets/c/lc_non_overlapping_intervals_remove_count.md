# LC Non Overlapping Intervals Remove Count

## Problem

Return the minimum number of intervals to remove so the rest do not overlap.

## Requirements

- Intervals are encoded as `start,end;...`.
- Use half-open overlap semantics matching the original problem examples.

## Source

- Source: LeetCode problem `non-overlapping-intervals`.
- URL: https://leetcode.com/problems/non-overlapping-intervals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_non_overlapping_intervals_remove_count(const char *intervals) {
    int a[256][2], n = 0, i = 0; while (intervals[i] != '\0') { for (int k = 0; k < 2; k++) { int sign = 1, v = 0; if (intervals[i] == '-') { sign = -1; i++; } while (intervals[i] >= '0' && intervals[i] <= '9') { v = v * 10 + intervals[i] - '0'; i++; } a[n][k] = sign * v; if (intervals[i] == ',') i++; } n++; if (intervals[i] == ';') i++; }
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y][1] < a[x][1]) { int s = a[x][0], e = a[x][1]; a[x][0] = a[y][0]; a[x][1] = a[y][1]; a[y][0] = s; a[y][1] = e; }
    int keep = 0, end = -2147483647; for (int x = 0; x < n; x++) if (a[x][0] >= end) { keep++; end = a[x][1]; } return n - keep;
}
```
