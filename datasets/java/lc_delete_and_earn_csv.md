# LC Delete And Earn CSV

## Problem

Return the maximum points from the delete-and-earn rule.

## Requirements

- `nums` is a nonempty comma-separated list of positive integers less than 1000.

## Source

- Source: LeetCode problem `delete-and-earn`.
- URL: https://leetcode.com/problems/delete-and-earn/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcDeleteAndEarnCsv {
    public static int lc_delete_and_earn_csv(String nums) {
        int[] points = new int[1000]; int max = 0; for (String p : nums.split(",")) { int v = Integer.parseInt(p); points[v] += v; if (v > max) max = v; } int take = 0, skip = 0; for (int v = 1; v <= max; v++) { int ntake = skip + points[v], nskip = Math.max(take, skip); take = ntake; skip = nskip; } return Math.max(take, skip);
    }
}
```
