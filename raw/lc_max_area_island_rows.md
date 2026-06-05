# LC Max Area Of Island Rows

## Problem

Return the maximum area of a 4-directionally connected island in a 0/1 grid.

## Requirements

- Rows are semicolon-separated.
- Rows contain only `0` and `1`.

## Source

- Source: LeetCode problem `max-area-of-island`.
- URL: https://leetcode.com/problems/max-area-of-island/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_max_area_island_rows(const char *rows) {
    char g[64][64]; int r = 0, c = 0, cols = 0, i = 0; while (rows[i] != '\0') { c = 0; while (rows[i] == '0' || rows[i] == '1') { g[r][c] = rows[i++]; c++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int best = 0, sx[4096], sy[4096]; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (g[x][y] == '1') { int area = 0, top = 0; sx[top] = x; sy[top] = y; top++; g[x][y] = '0'; while (top > 0) { top--; int cx = sx[top], cy = sy[top]; area++; int dx[4] = {1,-1,0,0}, dy[4] = {0,0,1,-1}; for (int k = 0; k < 4; k++) { int nx = cx + dx[k], ny = cy + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < cols && g[nx][ny] == '1') { g[nx][ny] = '0'; sx[top] = nx; sy[top] = ny; top++; } } } if (area > best) best = area; }
    return best;
}
```
