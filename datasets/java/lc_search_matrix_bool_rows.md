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

```java
class LcSearchMatrixBoolRows {
    public static boolean lc_search_matrix_bool_rows(String rows, int target) {
        String flat = rows.replace(';', ','); String[] p = flat.split(","); int l = 0, r = p.length - 1; while (l <= r) { int m = l + (r - l) / 2; int v = Integer.parseInt(p[m]); if (v == target) return true; if (v < target) l = m + 1; else r = m - 1; } return false;
    }
}
```
