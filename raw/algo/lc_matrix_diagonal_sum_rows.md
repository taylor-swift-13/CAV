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

```c
int lc_matrix_diagonal_sum_rows(const char *rows) {
    int a[64][64], n = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] != '\0' && rows[i] != ';') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + (rows[i] - '0'); i++; } a[n][c] = sign * v; c++; if (rows[i] == ',') i++; } if (cols == 0) cols = c; n++; if (rows[i] == ';') i++; } int sum = 0; for (int x = 0; x < n; x++) { sum += a[x][x]; if (x != n - 1 - x) sum += a[x][n - 1 - x]; } return sum;
}
```
