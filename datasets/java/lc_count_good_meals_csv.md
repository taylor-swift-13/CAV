# LC Count Good Meals CSV

## Problem

Return the number of pairs whose sum is a power of two.

## Requirements

- `deliciousness` is a comma-separated list of nonnegative integers.
- The supplied counts fit in signed 32-bit range.

## Source

- Source: LeetCode problem `count-good-meals`.
- URL: https://leetcode.com/problems/count-good-meals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcCountGoodMealsCsv {
    public static int lc_count_good_meals_csv(String deliciousness) {
        String[] p = deliciousness.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int ans = 0; for (int i = 0; i < a.length; i++) for (int j = i + 1; j < a.length; j++) { int s = a[i] + a[j]; if (s > 0 && (s & (s - 1)) == 0) ans++; } return ans;
    }
}
```
