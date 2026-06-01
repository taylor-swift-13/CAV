# Exercism Saddle Points Count Rows

## Problem

Count saddle points in an integer matrix.

## Requirements

- Rows are semicolon-separated and values inside a row are comma-separated.
- A saddle point is at least every value in its row and at most every value in its column.

## Source

- Source: Exercism problem `saddle-points`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/saddle-points
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExSaddlePointsCountRows {
    public static int ex_saddle_points_count_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].split(",").length; int[][] a = new int[r][c]; for (int i = 0; i < r; i++) { String[] p = rs[i].split(","); for (int j = 0; j < c; j++) a[i][j] = Integer.parseInt(p[j]); }
        int ans = 0; for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) { boolean ok = true; for (int y = 0; y < c; y++) if (a[i][y] > a[i][j]) ok = false; for (int x = 0; x < r; x++) if (a[x][j] < a[i][j]) ok = false; if (ok) ans++; } return ans;
    }
}
```
