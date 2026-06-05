# LC Insert Interval Total Length

## Problem

Insert a new interval, merge overlaps, and return the total covered length.

## Requirements

- Existing intervals are encoded as `start,end;...`.
- Existing intervals are sorted and non-overlapping.

## Source

- Source: LeetCode problem `insert-interval`.
- URL: https://leetcode.com/problems/insert-interval/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_insert_interval_total_length(const char *intervals, int new_start, int new_end) {
    int a[256][2], n = 0, i = 0; while (intervals[i] != '\0') { for (int k = 0; k < 2; k++) { int sign = 1, v = 0; if (intervals[i] == '-') { sign = -1; i++; } while (intervals[i] >= '0' && intervals[i] <= '9') { v = v * 10 + (intervals[i] - '0'); i++; } a[n][k] = sign * v; if (intervals[i] == ',') i++; } n++; if (intervals[i] == ';') i++; } a[n][0] = new_start; a[n][1] = new_end; n++;
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y][0] < a[x][0]) { int s = a[x][0], e = a[x][1]; a[x][0] = a[y][0]; a[x][1] = a[y][1]; a[y][0] = s; a[y][1] = e; }
    int total = 0, cs = a[0][0], ce = a[0][1]; for (int x = 1; x < n; x++) { if (a[x][0] <= ce) { if (a[x][1] > ce) ce = a[x][1]; } else { total += ce - cs; cs = a[x][0]; ce = a[x][1]; } } return total + ce - cs;
}
```
