# LC Shortest Path Binary Matrix Rows

## Problem

Return the shortest 8-direction path length from top-left to bottom-right, or `-1`.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.
- `0` means open and `1` means blocked.

## Source

- Source: LeetCode problem `shortest-path-in-binary-matrix`.
- URL: https://leetcode.com/problems/shortest-path-in-binary-matrix/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_shortest_path_binary_matrix_rows(const char *rows) {
    char g[64][64]; int n = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] == '0' || rows[i] == '1') { g[n][c] = rows[i++]; c++; } if (cols == 0) cols = c; n++; if (rows[i] == ';') i++; } if (g[0][0] == '1' || g[n - 1][cols - 1] == '1') return -1;
    int qx[4096], qy[4096], qd[4096], head = 0, tail = 0; qx[tail] = 0; qy[tail] = 0; qd[tail] = 1; tail++; g[0][0] = '1'; int dx[8] = {1,1,1,0,0,-1,-1,-1}, dy[8] = {-1,0,1,-1,1,-1,0,1}; while (head < tail) { int x = qx[head], y = qy[head], d = qd[head++]; if (x == n - 1 && y == cols - 1) return d; for (int t = 0; t < 8; t++) { int nx = x + dx[t], ny = y + dy[t]; if (nx >= 0 && nx < n && ny >= 0 && ny < cols && g[nx][ny] == '0') { g[nx][ny] = '1'; qx[tail] = nx; qy[tail] = ny; qd[tail] = d + 1; tail++; } } } return -1;
}
```
