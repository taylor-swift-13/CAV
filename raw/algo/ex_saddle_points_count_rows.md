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

```c
int ex_saddle_points_count_rows(const char *rows) {
    int a[32][32], r = 0, c = 0, cols = 0, i = 0;
    while (rows[i] != '\0') { c = 0; while (rows[i] != '\0' && rows[i] != ';') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + (rows[i] - '0'); i++; } a[r][c] = sign * v; c++; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int ans = 0; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) { int ok = 1; for (int j = 0; j < cols; j++) if (a[x][j] > a[x][y]) ok = 0; for (int j = 0; j < r; j++) if (a[j][y] < a[x][y]) ok = 0; if (ok) ans++; }
    return ans;
}
```
