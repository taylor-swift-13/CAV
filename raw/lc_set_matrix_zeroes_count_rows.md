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

```c
int lc_set_matrix_zeroes_count_rows(const char *rows) {
    int row[64] = {0}, col[64] = {0}, r = 0, c = 0, cols = 0, i = 0;
    while (rows[i] != '\0') { c = 0; while (rows[i] != '\0' && rows[i] != ';') { int v = 0; while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } if (v == 0) { row[r] = 1; col[c] = 1; } c++; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int zeros = 0; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (row[x] || col[y]) zeros++;
    return zeros;
}
```
