# LC Minimum Height Trees Root Count

## Problem

Return the number of roots that produce minimum-height trees.

## Requirements

- `edges` is semicolon-separated undirected `u,v` pairs.
- The graph is a tree with `n` nodes.

## Source

- Source: LeetCode problem `minimum-height-trees`.
- URL: https://leetcode.com/problems/minimum-height-trees/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMinHeightTreesRootCount {
    public static int lc_min_height_trees_root_count(int n, String edges) {
        int[][] g = new int[n][n]; int[] deg = new int[n]; for (String e : edges.split(";")) { String[] p = e.split(","); int a = Integer.parseInt(p[0]), b = Integer.parseInt(p[1]); g[a][b] = g[b][a] = 1; deg[a]++; deg[b]++; } int left = n, count = 0; int[] leaves = new int[n]; for (int v = 0; v < n; v++) if (deg[v] <= 1) leaves[count++] = v; while (left > 2) { left -= count; int[] next = new int[n]; int nc = 0; for (int k = 0; k < count; k++) for (int to = 0; to < n; to++) if (g[leaves[k]][to] == 1 && --deg[to] == 1) next[nc++] = to; leaves = next; count = nc; } return left;
    }
}
```
