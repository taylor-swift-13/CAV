# LC House Robber II CSV

## Problem

Return the maximum amount that can be robbed from circularly arranged houses.

## Requirements

- `nums` is a nonempty comma-separated list of nonnegative integers.
- Adjacent houses in the circle cannot both be robbed.

## Source

- Source: LeetCode problem `house-robber-ii`.
- URL: https://leetcode.com/problems/house-robber-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcHouseRobberIiCsv {
    public static int lc_house_robber_ii_csv(String nums) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); if (a.length == 1) return a[0];
        int prev = 0, cur = 0; for (int i = 0; i < a.length - 1; i++) { int next = Math.max(prev + a[i], cur); prev = cur; cur = next; } int best = cur;
        prev = 0; cur = 0; for (int i = 1; i < a.length; i++) { int next = Math.max(prev + a[i], cur); prev = cur; cur = next; } return Math.max(best, cur);
    }
}
```
