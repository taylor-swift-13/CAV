# LC Wiggle Subsequence Max Length CSV

## Problem

Return the length of the longest wiggle subsequence.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `wiggle-subsequence`.
- URL: https://leetcode.com/problems/wiggle-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcWiggleMaxLengthCsv {
    public static int lc_wiggle_max_length_csv(String nums) {
        String[] p = nums.split(","); int up = 1, down = 1, prev = Integer.parseInt(p[0]); for (int i = 1; i < p.length; i++) { int x = Integer.parseInt(p[i]); if (x > prev) up = down + 1; else if (x < prev) down = up + 1; prev = x; } return Math.max(up, down);
    }
}
```
