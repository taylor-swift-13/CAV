# LC Path With Minimum Effort Rows

## Problem

Return the minimum possible maximum absolute height difference along a path.

## Requirements

- Heights are encoded as semicolon-separated comma rows.
- Moves are 4-directional from top-left to bottom-right.

## Source

- Source: LeetCode problem `path-with-minimum-effort`.
- URL: https://leetcode.com/problems/path-with-minimum-effort/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_minimum_effort_path_rows(const char *rows) {
    int a[64][64], r = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] != '\0' && rows[i] != ';') { int v = 0; while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[r][c++] = v; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int total = r * cols, dist[4096], used[4096] = {0}; for (int x = 0; x < total; x++) dist[x] = 1000000000; dist[0] = 0; int dx[4] = {1,-1,0,0}, dy[4] = {0,0,1,-1}; for (int step = 0; step < total; step++) { int node = -1; for (int x = 0; x < total; x++) if (!used[x] && (node < 0 || dist[x] < dist[node])) node = x; if (node == total - 1) break; used[node] = 1; int cr = node / cols, cc = node % cols; for (int d = 0; d < 4; d++) { int nr = cr + dx[d], nc = cc + dy[d]; if (nr >= 0 && nr < r && nc >= 0 && nc < cols) { int diff = a[cr][cc] > a[nr][nc] ? a[cr][cc] - a[nr][nc] : a[nr][nc] - a[cr][cc]; int nd = dist[node] > diff ? dist[node] : diff; int ni = nr * cols + nc; if (nd < dist[ni]) dist[ni] = nd; } } } return dist[total - 1];
}
```
