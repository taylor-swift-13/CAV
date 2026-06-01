# LC Single Number II CSV

## Problem

Return the element that appears once when every other element appears three times.

## Requirements

- `nums` is a comma-separated list of signed integers.

## Source

- Source: LeetCode problem `single-number-ii`.
- URL: https://leetcode.com/problems/single-number-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcSingleNumberIiCsv {
    public static int lc_single_number_ii_csv(String nums) {
        int ones = 0, twos = 0; for (String part : nums.split(",")) { int v = Integer.parseInt(part); ones = (ones ^ v) & ~twos; twos = (twos ^ v) & ~ones; } return ones;
    }
}
```
