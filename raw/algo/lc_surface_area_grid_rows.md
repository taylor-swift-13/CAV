# LC Surface Area 3D Shapes Rows

## Problem

Return the surface area of stacked cubes in a grid.

## Requirements

- Rows are semicolon-separated comma lists of nonnegative heights.

## Source

- Source: LeetCode problem `surface-area-of-3d-shapes`.
- URL: https://leetcode.com/problems/surface-area-of-3d-shapes/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_surface_area_grid_rows(const char *rows) {
    int a[64][64], r = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] != '\0' && rows[i] != ';') { int v = 0; while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + (rows[i] - '0'); i++; } a[r][c] = v; c++; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; } int area = 0; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (a[x][y] > 0) { area += 2 + 4 * a[x][y]; if (x > 0) area -= 2 * (a[x][y] < a[x - 1][y] ? a[x][y] : a[x - 1][y]); if (y > 0) area -= 2 * (a[x][y] < a[x][y - 1] ? a[x][y] : a[x][y - 1]); } return area;
}
```
