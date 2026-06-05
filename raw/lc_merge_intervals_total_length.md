# LC Merge Intervals Total Length

## Problem

Merge overlapping intervals and return the total covered length.

## Requirements

- Intervals are encoded as `start,end;...`.
- Touching intervals merge as in the original problem.

## Source

- Source: LeetCode problem `merge-intervals`.
- URL: https://leetcode.com/problems/merge-intervals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_merge_intervals_total_length(const char *intervals) {
    int a[256][2], n = 0, i = 0; while (intervals[i] != '\0') { for (int k = 0; k < 2; k++) { int sign = 1, v = 0; if (intervals[i] == '-') { sign = -1; i++; } while (intervals[i] >= '0' && intervals[i] <= '9') { v = v * 10 + (intervals[i] - '0'); i++; } a[n][k] = sign * v; if (intervals[i] == ',') i++; } n++; if (intervals[i] == ';') i++; }
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y][0] < a[x][0]) { int s = a[x][0], e = a[x][1]; a[x][0] = a[y][0]; a[x][1] = a[y][1]; a[y][0] = s; a[y][1] = e; }
    int total = 0, cs = a[0][0], ce = a[0][1]; for (int x = 1; x < n; x++) { if (a[x][0] <= ce) { if (a[x][1] > ce) ce = a[x][1]; } else { total += ce - cs; cs = a[x][0]; ce = a[x][1]; } } return total + ce - cs;
}
```
