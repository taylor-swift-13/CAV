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

```java
class LcProjectionAreaRows {
    public static int lc_projection_area_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].split(",").length; int[][] a = new int[r][c]; int xy = 0, yz = 0, zx = 0; for (int i = 0; i < r; i++) { String[] p = rs[i].split(","); int rowMax = 0; for (int j = 0; j < c; j++) { a[i][j] = Integer.parseInt(p[j]); if (a[i][j] > 0) xy++; rowMax = Math.max(rowMax, a[i][j]); } yz += rowMax; } for (int j = 0; j < c; j++) { int colMax = 0; for (int i = 0; i < r; i++) colMax = Math.max(colMax, a[i][j]); zx += colMax; } return xy + yz + zx;
    }
}
```
