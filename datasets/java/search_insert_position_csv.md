# search_insert_position_csv

## Problem

Given a sorted comma-separated integer array `nums`, return the index of `target` or where it should be inserted.

## Requirements

- `nums` is sorted in strictly increasing order.
- The empty string represents an empty array.
- Return the first index whose value is at least `target`.
- If all values are smaller, return the array length.

## Source

- Source: LeetCode problem `search-insert-position`.
- URL: https://leetcode.com/problems/search-insert-position/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class SearchInsertPositionCsv {
    public static int search_insert_position_csv(String nums, int target) {
        if (nums.isEmpty()) return 0;
        String[] parts = nums.split(",");
        for (int i = 0; i < parts.length; i++) if (Integer.parseInt(parts[i]) >= target) return i;
        return parts.length;
    }
}
```
