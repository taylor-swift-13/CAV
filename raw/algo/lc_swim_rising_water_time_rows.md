# LC Swim In Rising Water Time Rows

## Problem

Return the minimum time needed to reach the bottom-right cell.

## Requirements

- Grid values are encoded as semicolon-separated comma rows.
- You may move 4-directionally through cells whose value is at most the current time.

## Source

- Source: LeetCode problem `swim-in-rising-water`.
- URL: https://leetcode.com/problems/swim-in-rising-water/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_swim_rising_water_time_rows(const char *rows) {
    int a[64][64], r = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] != '\0' && rows[i] != ';') { int v = 0; while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + (rows[i] - '0'); i++; } a[r][c] = v; c++; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int total = r * cols, dist[4096], used[4096] = {0}; for (int x = 0; x < total; x++) dist[x] = 1000000000; dist[0] = a[0][0]; int dx[4] = {1,-1,0,0}, dy[4] = {0,0,1,-1}; for (int step = 0; step < total; step++) { int node = -1; for (int x = 0; x < total; x++) if (!used[x] && (node < 0 || dist[x] < dist[node])) node = x; if (node == total - 1) break; used[node] = 1; int cr = node / cols, cc = node % cols; for (int d = 0; d < 4; d++) { int nr = cr + dx[d], nc = cc + dy[d]; if (nr >= 0 && nr < r && nc >= 0 && nc < cols) { int ni = nr * cols + nc; int nd = dist[node] > a[nr][nc] ? dist[node] : a[nr][nc]; if (nd < dist[ni]) dist[ni] = nd; } } } return dist[total - 1];
}
```
