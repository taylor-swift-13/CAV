# LC Min Cost Climbing Stairs CSV

## Problem

Return the minimum cost to reach the top of the staircase.

## Requirements

- `cost` is a comma-separated list of nonnegative integers.
- You may start at step 0 or step 1.

## Source

- Source: LeetCode problem `min-cost-climbing-stairs`.
- URL: https://leetcode.com/problems/min-cost-climbing-stairs/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMinCostClimbingStairsCsv {
    public static int lc_min_cost_climbing_stairs_csv(String cost) {
        String[] p = cost.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int p2 = 0, p1 = 0; for (int i = 2; i <= a.length; i++) { int cur = Math.min(p1 + a[i - 1], p2 + a[i - 2]); p2 = p1; p1 = cur; } return p1;
    }
}
```
