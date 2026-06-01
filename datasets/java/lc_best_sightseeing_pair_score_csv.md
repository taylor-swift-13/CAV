# LC Best Sightseeing Pair Score CSV

## Problem

Return the maximum score `values[i] + values[j] + i - j` for `i < j`.

## Requirements

- `values` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `best-sightseeing-pair`.
- URL: https://leetcode.com/problems/best-sightseeing-pair/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcBestSightseeingPairScoreCsv {
    public static int lc_best_sightseeing_pair_score_csv(String values) {
        String[] p = values.split(","); int bestLeft = Integer.parseInt(p[0]), ans = Integer.MIN_VALUE; for (int j = 1; j < p.length; j++) { int v = Integer.parseInt(p[j]); ans = Math.max(ans, bestLeft + v - j); bestLeft = Math.max(bestLeft, v + j); } return ans;
    }
}
```
