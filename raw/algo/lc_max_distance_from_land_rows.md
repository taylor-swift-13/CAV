# LC As Far From Land As Possible Rows

## Problem

Return the maximum Manhattan distance from any water cell to nearest land, or `-1` if no answer exists.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.
- `1` is land and `0` is water.

## Source

- Source: LeetCode problem `as-far-from-land-as-possible`.
- URL: https://leetcode.com/problems/as-far-from-land-as-possible/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_max_distance_from_land_rows(const char *rows) {
    char g[64][64]; int r = 0, cols = 0, i = 0, qx[4096], qy[4096], qd[4096], head = 0, tail = 0, water = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] == '0' || rows[i] == '1') { g[r][c] = rows[i]; if (g[r][c] == '1') { qx[tail] = r; qy[tail] = c; qd[tail] = 0; tail++; } else water++; c++; i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; } if (tail == 0 || water == 0) return -1;
    int ans = 0, dx[4] = {1,-1,0,0}, dy[4] = {0,0,1,-1}; while (head < tail) { int x = qx[head], y = qy[head], d = qd[head++]; if (d > ans) ans = d; for (int k = 0; k < 4; k++) { int nx = x + dx[k], ny = y + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < cols && g[nx][ny] == '0') { g[nx][ny] = '1'; qx[tail] = nx; qy[tail] = ny; qd[tail] = d + 1; tail++; } } } return ans;
}
```
