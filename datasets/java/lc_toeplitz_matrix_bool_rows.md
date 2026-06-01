# LC Toeplitz Matrix Bool Rows

## Problem

Return true if every diagonal from top-left to bottom-right has the same value.

## Requirements

- Rows are semicolon-separated and values in a row are comma-separated.
- All rows have equal positive length.

## Source

- Source: LeetCode problem `toeplitz-matrix`.
- URL: https://leetcode.com/problems/toeplitz-matrix/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcToeplitzMatrixBoolRows {
    public static boolean lc_toeplitz_matrix_bool_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].split(",").length; int[][] a = new int[r][c]; for (int i = 0; i < r; i++) { String[] p = rs[i].split(","); for (int j = 0; j < c; j++) a[i][j] = Integer.parseInt(p[j]); }
        for (int i = 1; i < r; i++) for (int j = 1; j < c; j++) if (a[i][j] != a[i - 1][j - 1]) return false; return true;
    }
}
```
