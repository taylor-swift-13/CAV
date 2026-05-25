# count_good_pairs_csv

## Problem

Return the number of index pairs `(i,j)` with `i < j` and equal values in comma-separated integer array `nums`.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Count pairs of distinct indices with equal values.
- Return the pair count, not the values.

## Source

- Source: LeetCode problem `number-of-good-pairs`.
- URL: https://leetcode.com/problems/number-of-good-pairs/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class CountGoodPairsCsv {
    public static int count_good_pairs_csv(String nums) {
        if (nums.isEmpty()) return 0;
        String[] parts = nums.split(",");
        int count = 0;
        for (int i = 0; i < parts.length; i++) for (int j = i + 1; j < parts.length; j++) if (parts[i].equals(parts[j])) count++;
        return count;
    }
}
```
