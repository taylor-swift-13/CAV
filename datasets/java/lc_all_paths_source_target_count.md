# LC All Paths Source Target Count

## Problem

Return how many directed paths go from node `0` to node `n-1` in a DAG.

## Requirements

- Adjacency lists are semicolon-separated.
- Neighbors inside a list are comma-separated; `-` means no outgoing edges.

## Source

- Source: LeetCode problem `all-paths-from-source-to-target`.
- URL: https://leetcode.com/problems/all-paths-from-source-to-target/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcAllPathsSourceTargetCount {
    static int dfs(int v, int n, int[][] g, int[] deg, int[] memo) { if (v == n - 1) return 1; if (memo[v] >= 0) return memo[v]; int ans = 0; for (int i = 0; i < deg[v]; i++) ans += dfs(g[v][i], n, g, deg, memo); return memo[v] = ans; }
    public static int lc_all_paths_source_target_count(String graph) {
        String[] rows = graph.split(";"); int n = rows.length; int[][] g = new int[n][n]; int[] deg = new int[n]; for (int i = 0; i < n; i++) if (!rows[i].equals("-")) for (String p : rows[i].split(",")) g[i][deg[i]++] = Integer.parseInt(p); int[] memo = new int[n]; java.util.Arrays.fill(memo, -1); return dfs(0, n, g, deg, memo);
    }
}
```
