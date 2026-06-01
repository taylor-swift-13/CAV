# LC Fruit Into Baskets Length CSV

## Problem

Return the longest contiguous subarray containing at most two distinct fruit types.

## Requirements

- `fruits` is a comma-separated list of integer fruit types.

## Source

- Source: LeetCode problem `fruit-into-baskets`.
- URL: https://leetcode.com/problems/fruit-into-baskets/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcFruitIntoBasketsLenCsv {
    public static int lc_fruit_into_baskets_len_csv(String fruits) {
        String[] p = fruits.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int best = 0; for (int l = 0; l < a.length; l++) { int t1 = -1, t2 = -1; for (int r = l; r < a.length; r++) { if (a[r] == t1 || a[r] == t2) { } else if (t1 == -1) t1 = a[r]; else if (t2 == -1) t2 = a[r]; else break; best = Math.max(best, r - l + 1); } } return best;
    }
}
```
