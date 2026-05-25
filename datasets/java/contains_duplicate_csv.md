# contains_duplicate_csv

## Problem

Return true if comma-separated integer string `nums` contains the same value at least twice.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Return true if any two distinct positions contain equal values.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `contains-duplicate`.
- URL: https://leetcode.com/problems/contains-duplicate/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ContainsDuplicateCsv {
    public static boolean contains_duplicate_csv(String nums) {
        if (nums.isEmpty()) return false;
        String[] parts = nums.split(",");
        for (int i = 0; i < parts.length; i++) for (int j = i + 1; j < parts.length; j++) if (parts[i].equals(parts[j])) return true;
        return false;
    }
}
```
