# LC Longest Turbulent Subarray Length CSV

## Problem

Return the length of the longest turbulent subarray.

## Requirements

- Adjacent comparisons must alternate between greater-than and less-than.

## Source

- Source: LeetCode problem `longest-turbulent-subarray`.
- URL: https://leetcode.com/problems/longest-turbulent-subarray/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcTurbulentSubarrayLenCsv {
    public static int lc_turbulent_subarray_len_csv(String arr) {
        String[] p = arr.split(","); int up = 1, down = 1, best = 1, prev = Integer.parseInt(p[0]); for (int i = 1; i < p.length; i++) { int x = Integer.parseInt(p[i]); if (x > prev) { up = down + 1; down = 1; } else if (x < prev) { down = up + 1; up = 1; } else { up = 1; down = 1; } best = Math.max(best, Math.max(up, down)); prev = x; } return best;
    }
}
```
