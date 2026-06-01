# LC Largest Plus Sign Order

## Problem

Return the order of the largest axis-aligned plus sign.

## Requirements

- Mines are encoded as `r,c;...`; use `-` for no mines.
- Grid size is `n x n`.

## Source

- Source: LeetCode problem `order-of-largest-plus-sign`.
- URL: https://leetcode.com/problems/order-of-largest-plus-sign/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLargestPlusSignOrder {
    public static int lc_largest_plus_sign_order(int n, String mines) {
        int[][] g = new int[n][n]; for (int i = 0; i < n; i++) java.util.Arrays.fill(g[i], 1); if (!mines.equals("-")) for (String row : mines.split(";")) { String[] p = row.split(","); g[Integer.parseInt(p[0])][Integer.parseInt(p[1])] = 0; } int best = 0; for (int x = 0; x < n; x++) for (int y = 0; y < n; y++) if (g[x][y] == 1) { int order = 1; while (x - order >= 0 && x + order < n && y - order >= 0 && y + order < n && g[x - order][y] == 1 && g[x + order][y] == 1 && g[x][y - order] == 1 && g[x][y + order] == 1) order++; best = Math.max(best, order); } return best;
    }
}
```
