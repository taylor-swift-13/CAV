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

```java
class LcShortestPathBinaryMatrixRows {
    public static int lc_shortest_path_binary_matrix_rows(String rows) {
        String[] rs = rows.split(";"); int n = rs.length, c = rs[0].length(); char[][] g = new char[n][c]; for (int i = 0; i < n; i++) g[i] = rs[i].toCharArray(); if (g[0][0] == '1' || g[n - 1][c - 1] == '1') return -1; int[] qx = new int[n * c], qy = new int[n * c], qd = new int[n * c], dx = {1,1,1,0,0,-1,-1,-1}, dy = {-1,0,1,-1,1,-1,0,1}; int head = 0, tail = 0; qx[tail] = 0; qy[tail] = 0; qd[tail++] = 1; g[0][0] = '1'; while (head < tail) { int x = qx[head], y = qy[head], d = qd[head++]; if (x == n - 1 && y == c - 1) return d; for (int t = 0; t < 8; t++) { int nx = x + dx[t], ny = y + dy[t]; if (nx >= 0 && nx < n && ny >= 0 && ny < c && g[nx][ny] == '0') { g[nx][ny] = '1'; qx[tail] = nx; qy[tail] = ny; qd[tail++] = d + 1; } } } return -1;
    }
}
```
