# LC Kth Smallest Matrix Rows

## Problem

Return the `k`th smallest element in a sorted matrix.

## Requirements

- Rows are semicolon-separated comma lists.
- Rows and columns are sorted ascending.

## Source

- Source: LeetCode problem `kth-smallest-element-in-a-sorted-matrix`.
- URL: https://leetcode.com/problems/kth-smallest-element-in-a-sorted-matrix/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_kth_smallest_matrix_rows(const char *rows, int k) {
    int a[4096], n = 0, i = 0; while (rows[i] != '\0') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + (rows[i] - '0'); i++; } a[n++] = sign * v; if (rows[i] == ',' || rows[i] == ';') i++; }
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; }
    return a[k - 1];
}
```
