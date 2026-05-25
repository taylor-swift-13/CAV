# single_number_csv

## Problem

In a comma-separated integer array where every value appears twice except one, return the single value.

## Requirements

- Input is nonempty.
- Exactly one value appears once and every other value appears twice.
- Values are base-10 integers with no spaces.
- Return the unique value.

## Source

- Source: LeetCode problem `single-number`.
- URL: https://leetcode.com/problems/single-number/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class SingleNumberCsv {
    public static int single_number_csv(String nums) {
        int x = 0;
        for (String p : nums.split(",")) x ^= Integer.parseInt(p);
        return x;
    }
}
```
