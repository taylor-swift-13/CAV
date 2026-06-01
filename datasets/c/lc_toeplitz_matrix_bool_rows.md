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

```c
int lc_toeplitz_matrix_bool_rows(const char *rows) {
    int a[64][64], r = 0, c = 0, cols = 0, i = 0;
    while (rows[i] != '\0') { c = 0; while (rows[i] != '\0' && rows[i] != ';') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[r][c++] = sign * v; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    for (int x = 1; x < r; x++) {
        for (int y = 1; y < cols; y++) if (a[x][y] != a[x - 1][y - 1]) return 0;
    }
    return 1;
}
```
