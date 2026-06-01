# LC Set Matrix Zeroes Count Rows

## Problem

Apply the set-matrix-zeroes rule to a semicolon-separated 0/1 matrix and return the final number of zero cells.

## Requirements

- Rows use comma-separated `0` or `1` values.
- All rows have equal positive length.

## Source

- Source: LeetCode problem `set-matrix-zeroes`.
- URL: https://leetcode.com/problems/set-matrix-zeroes/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcSetMatrixZeroesCountRows {
    public static int lc_set_matrix_zeroes_count_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].split(",").length; boolean[] row = new boolean[r], col = new boolean[c]; int[][] a = new int[r][c];
        for (int i = 0; i < r; i++) { String[] p = rs[i].split(","); for (int j = 0; j < c; j++) { a[i][j] = Integer.parseInt(p[j]); if (a[i][j] == 0) { row[i] = true; col[j] = true; } } }
        int zeros = 0; for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (row[i] || col[j]) zeros++; return zeros;
    }
}
```
