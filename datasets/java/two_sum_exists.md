# two_sum_exists

## Problem

Return true if two distinct elements in integer array string `nums` sum to `target`.

## Requirements

- `nums` is encoded as comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- A valid pair must use two distinct positions, even if the values are equal.
- Return only whether such a pair exists; do not return indices.
- The number of encoded integers is at most 64 in this dataset variant.

## Source

- Source: LeetCode problem `two-sum`.
- URL: https://leetcode.com/problems/two-sum/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class TwoSumExists {
    public static boolean two_sum_exists(String nums, int target) {
        String[] parts = nums.isEmpty() ? new String[0] : nums.split(",");
        int[] values = new int[parts.length];
        for (int i = 0; i < parts.length; i++) values[i] = Integer.parseInt(parts[i]);
        for (int i = 0; i < values.length; i++) for (int j = i + 1; j < values.length; j++) if (values[i] + values[j] == target) return true;
        return false;
    }
}
```
