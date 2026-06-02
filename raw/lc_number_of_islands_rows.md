# LC Number Of Islands Rows

## Problem

Count 4-directionally connected islands of `1` cells in a semicolon-separated binary grid.

## Requirements

- Rows contain only `0` and `1`.
- All rows have equal positive length.
- The empty string returns `0`.

## Source

- Source: LeetCode problem `number-of-islands`.
- URL: https://leetcode.com/problems/number-of-islands/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_number_of_islands_rows(const char *rows) {
    if (rows[0] == '\0') return 0;
    char g[64][64]; int r = 0, c = 0, cols = 0, i = 0;
    while (rows[i] != '\0') { c = 0; while (rows[i] == '0' || rows[i] == '1') g[r][c++] = rows[i++]; if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int ans = 0, sx[4096], sy[4096];
    for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (g[x][y] == '1') { ans++; int top = 0; sx[top] = x; sy[top++] = y; g[x][y] = '0'; while (top > 0) { top--; int cx = sx[top], cy = sy[top]; int dx[4] = {1,-1,0,0}, dy[4] = {0,0,1,-1}; for (int k = 0; k < 4; k++) { int nx = cx + dx[k], ny = cy + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < cols && g[nx][ny] == '1') { g[nx][ny] = '0'; sx[top] = nx; sy[top++] = ny; } } } }
    return ans;
}
```
