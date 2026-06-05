# LC Projection Area 3D Shapes Rows

## Problem

Return the total projection area of a 3D shape grid.

## Requirements

- Rows are semicolon-separated comma lists of nonnegative heights.

## Source

- Source: LeetCode problem `projection-area-of-3d-shapes`.
- URL: https://leetcode.com/problems/projection-area-of-3d-shapes/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_projection_area_rows(const char *rows) {
    int a[64][64], r = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] != '\0' && rows[i] != ';') { int v = 0; while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[r][c++] = v; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; } int xy = 0, yz = 0, zx = 0; for (int x = 0; x < r; x++) { int rowmax = 0; for (int y = 0; y < cols; y++) { if (a[x][y] > 0) xy++; if (a[x][y] > rowmax) rowmax = a[x][y]; } yz += rowmax; } for (int y = 0; y < cols; y++) { int colmax = 0; for (int x = 0; x < r; x++) if (a[x][y] > colmax) colmax = a[x][y]; zx += colmax; } return xy + yz + zx;
}
```
