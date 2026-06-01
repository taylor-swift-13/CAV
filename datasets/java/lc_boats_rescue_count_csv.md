# LC Boats To Save People Count CSV

## Problem

Return the minimum number of boats needed to rescue everyone.

## Requirements

- `people` is a comma-separated list of weights.
- Each boat carries at most two people with total weight at most `limit`.

## Source

- Source: LeetCode problem `boats-to-save-people`.
- URL: https://leetcode.com/problems/boats-to-save-people/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcBoatsRescueCountCsv {
    public static int lc_boats_rescue_count_csv(String people, int limit) {
        String[] p = people.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a); int l = 0, r = a.length - 1, boats = 0; while (l <= r) { if (a[l] + a[r] <= limit) l++; r--; boats++; } return boats;
    }
}
```
