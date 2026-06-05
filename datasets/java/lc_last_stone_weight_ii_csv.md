# LC Last Stone Weight II CSV

## Problem

Return the smallest possible final stone weight.

## Requirements

- `stones` is a comma-separated list of positive weights.

## Source

- Source: LeetCode problem `last-stone-weight-ii`.
- URL: https://leetcode.com/problems/last-stone-weight-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLastStoneWeightIiCsv {
    public static int lc_last_stone_weight_ii_csv(String stones) {
        String[] p = stones.split(","); int[] a = new int[p.length]; int sum = 0; for (int i = 0; i < p.length; i++) { a[i] = Integer.parseInt(p[i]); sum += a[i]; } int[] dp = new int[sum / 2 + 1]; for (int v : a) for (int s = sum / 2; s >= v; s--) dp[s] = Math.max(dp[s], dp[s - v] + v); return sum - 2 * dp[sum / 2];
    }
}
```
