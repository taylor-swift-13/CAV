# LC Longest Increasing Path Matrix

## Problem

Return the length of the longest strictly increasing 4-directional path in a matrix.

## Requirements

- Rows are semicolon-separated comma lists of signed integers.

## Source

- Source: LeetCode problem `longest-increasing-path-in-a-matrix`.
- URL: https://leetcode.com/problems/longest-increasing-path-in-a-matrix/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
static int lc_lip_dfs(int x, int y, int r, int c, int a[64][64], int memo[64][64]) { if (memo[x][y]) return memo[x][y]; int best = 1, dx[4] = {1,-1,0,0}, dy[4] = {0,0,1,-1}; for (int k = 0; k < 4; k++) { int nx = x + dx[k], ny = y + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < c && a[nx][ny] > a[x][y]) { int cand = 1 + lc_lip_dfs(nx, ny, r, c, a, memo); if (cand > best) best = cand; } } memo[x][y] = best; return best; }
int lc_longest_increasing_path_matrix(const char *rows) {
    int a[64][64], r = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] != '\0' && rows[i] != ';') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + (rows[i] - '0'); i++; } a[r][c] = sign * v; c++; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; } int memo[64][64] = {{0}}, ans = 0; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) { int v = lc_lip_dfs(x, y, r, cols, a, memo); if (v > ans) ans = v; } return ans;
}
```
