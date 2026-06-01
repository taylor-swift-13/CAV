# LC Search A 2D Matrix Bool Rows

## Problem

Return true if `target` appears in a row-major sorted matrix.

## Requirements

- Rows are semicolon-separated.
- Numbers inside each row are comma-separated signed integers.

## Source

- Source: LeetCode problem `search-a-2d-matrix`.
- URL: https://leetcode.com/problems/search-a-2d-matrix/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_search_matrix_bool_rows(const char *rows, int target) {
    int a[4096], n = 0, i = 0; while (rows[i] != '\0') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[n++] = sign * v; if (rows[i] == ',' || rows[i] == ';') i++; }
    int l = 0, r = n - 1; while (l <= r) { int m = l + (r - l) / 2; if (a[m] == target) return 1; if (a[m] < target) l = m + 1; else r = m - 1; } return 0;
}
```
