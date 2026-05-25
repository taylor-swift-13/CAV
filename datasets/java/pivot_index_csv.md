# pivot_index_csv

## Problem

Return the leftmost pivot index of comma-separated integer array `nums`, or `-1` if none exists.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string has no pivot and returns `-1`.
- A pivot has equal sum strictly to its left and strictly to its right.
- Return the leftmost pivot index.

## Source

- Source: LeetCode problem `find-pivot-index`.
- URL: https://leetcode.com/problems/find-pivot-index/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class PivotIndexCsv {
    public static int pivot_index_csv(String nums) {
        if (nums.isEmpty()) return -1;
        String[] parts = nums.split(",");
        int total = 0;
        for (String p : parts) total += Integer.parseInt(p);
        int left = 0;
        for (int i = 0; i < parts.length; i++) { int v = Integer.parseInt(parts[i]); if (left == total - left - v) return i; left += v; }
        return -1;
    }
}
```
