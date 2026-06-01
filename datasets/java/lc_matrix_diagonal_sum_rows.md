# LC Matrix Diagonal Sum Rows

## Problem

Return the sum of both diagonals of a square matrix, counting the center once.

## Requirements

- Rows are semicolon-separated comma lists of integers.

## Source

- Source: LeetCode problem `matrix-diagonal-sum`.
- URL: https://leetcode.com/problems/matrix-diagonal-sum/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMatrixDiagonalSumRows {
    public static int lc_matrix_diagonal_sum_rows(String rows) {
        String[] rs = rows.split(";"); int n = rs.length, sum = 0; for (int i = 0; i < n; i++) { String[] p = rs[i].split(","); sum += Integer.parseInt(p[i]); if (i != n - 1 - i) sum += Integer.parseInt(p[n - 1 - i]); } return sum;
    }
}
```
