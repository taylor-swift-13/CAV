# LC Valid Mountain Array CSV

## Problem

Return true if comma-separated array `arr` is a valid mountain array.

## Requirements

- The empty string represents an empty array.
- A valid mountain has length at least `3`, strictly increases, then strictly decreases.

## Source

- Source: LeetCode problem `valid-mountain-array`.
- URL: https://leetcode.com/problems/valid-mountain-array/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcValidMountainArrayCsv {
    public static boolean lc_valid_mountain_array_csv(String arr) {
        if (arr.isEmpty()) return false;
        String[] parts = arr.split(",");
        int n = parts.length;
        if (n < 3) return false;
        int[] a = new int[n];
        for (int i = 0; i < n; i++) a[i] = Integer.parseInt(parts[i]);
        int p = 0;
        while (p + 1 < n && a[p] < a[p + 1]) p++;
        if (p == 0 || p == n - 1) return false;
        while (p + 1 < n && a[p] > a[p + 1]) p++;
        return p == n - 1;
    }
}
```
