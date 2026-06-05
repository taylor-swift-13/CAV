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

```c
int lc_min_cost_climbing_stairs_csv(const char *cost) {
    int a[256], n = 0, i = 0; while (cost[i] != '\0') { int v = 0; while (cost[i] >= '0' && cost[i] <= '9') { v = v * 10 + (cost[i] - '0'); i++; } a[n] = v; n++; if (cost[i] == ',') i++; }
    int p2 = 0, p1 = 0; for (int j = 2; j <= n; j++) { int x = p1 + a[j - 1], y = p2 + a[j - 2], cur = x < y ? x : y; p2 = p1; p1 = cur; } return p1;
}
```
