# LC Minimum Arrows Burst Balloons Count

## Problem

Return the minimum number of arrows needed to burst all balloons.

## Requirements

- Balloons are encoded as `start,end;...`.
- An arrow at coordinate `x` bursts every interval containing `x`.

## Source

- Source: LeetCode problem `minimum-number-of-arrows-to-burst-balloons`.
- URL: https://leetcode.com/problems/minimum-number-of-arrows-to-burst-balloons/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_arrows_burst_balloons_count(const char *points) {
    int a[512][2], n = 0, i = 0; while (points[i] != '\0') { for (int k = 0; k < 2; k++) { int sign = 1, v = 0; if (points[i] == '-') { sign = -1; i++; } while (points[i] >= '0' && points[i] <= '9') { v = v * 10 + points[i] - '0'; i++; } a[n][k] = sign * v; if (points[i] == ',') i++; } n++; if (points[i] == ';') i++; }
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y][1] < a[x][1]) { int s = a[x][0], e = a[x][1]; a[x][0] = a[y][0]; a[x][1] = a[y][1]; a[y][0] = s; a[y][1] = e; }
    int arrows = 0, end = -2147483647; for (int x = 0; x < n; x++) if (arrows == 0 || a[x][0] > end) { arrows++; end = a[x][1]; } return arrows;
}
```
