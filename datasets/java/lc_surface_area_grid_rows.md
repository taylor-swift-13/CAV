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

```java
class LcSurfaceAreaGridRows {
    public static int lc_surface_area_grid_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].split(",").length; int[][] a = new int[r][c]; for (int i = 0; i < r; i++) { String[] p = rs[i].split(","); for (int j = 0; j < c; j++) a[i][j] = Integer.parseInt(p[j]); } int area = 0; for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (a[i][j] > 0) { area += 2 + 4 * a[i][j]; if (i > 0) area -= 2 * Math.min(a[i][j], a[i - 1][j]); if (j > 0) area -= 2 * Math.min(a[i][j], a[i][j - 1]); } return area;
    }
}
```
