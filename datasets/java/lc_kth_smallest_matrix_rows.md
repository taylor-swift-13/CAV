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

```java
class LcKthSmallestMatrixRows {
    public static int lc_kth_smallest_matrix_rows(String rows, int k) {
        String[] p = rows.replace(';', ',').split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a); return a[k - 1];
    }
}
```
