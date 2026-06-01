# Exercism Binary Search Index CSV

## Problem

Return the index of `target` in a sorted comma-separated array, or `-1` if absent.

## Requirements

- The empty string represents an empty array.
- Values are sorted ascending.

## Source

- Source: Exercism problem `binary-search`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/binary-search
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExBinarySearchIndexCsv {
    public static int ex_binary_search_index_csv(String nums, int target) {
        if (nums.isEmpty()) return -1;
        String[] parts = nums.split(",");
        int l = 0, r = parts.length - 1;
        while (l <= r) { int m = l + (r - l) / 2; int v = Integer.parseInt(parts[m]); if (v == target) return m; if (v < target) l = m + 1; else r = m - 1; }
        return -1;
    }
}
```
