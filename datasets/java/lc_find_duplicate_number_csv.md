# LC Find Duplicate Number CSV

## Problem

Return the duplicated number in comma-separated `nums`.

## Requirements

- `nums` has length `n+1` and values in `1..n`.
- At least one duplicate exists.

## Source

- Source: LeetCode problem `find-the-duplicate-number`.
- URL: https://leetcode.com/problems/find-the-duplicate-number/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcFindDuplicateNumberCsv {
    public static int lc_find_duplicate_number_csv(String nums) {
        boolean[] seen = new boolean[2048]; for (String part : nums.split(",")) { int v = Integer.parseInt(part); if (seen[v]) return v; seen[v] = true; } return -1;
    }
}
```
