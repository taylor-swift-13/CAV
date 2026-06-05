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

```c
static int lc_paths_dfs(int v, int n, int g[64][64], int deg[64], int memo[64]) { if (v == n - 1) return 1; if (memo[v] >= 0) return memo[v]; int ans = 0; for (int i = 0; i < deg[v]; i++) ans += lc_paths_dfs(g[v][i], n, g, deg, memo); memo[v] = ans; return ans; }
int lc_all_paths_source_target_count(const char *graph) {
    int g[64][64], deg[64] = {0}, n = 0, i = 0; while (graph[i] != '\0') { if (graph[i] == '-') i++; else while (graph[i] != '\0' && graph[i] != ';') { int v = 0; while (graph[i] >= '0' && graph[i] <= '9') { v = v * 10 + (graph[i] - '0'); i++; } g[n][deg[n]++] = v; if (graph[i] == ',') i++; } n++; if (graph[i] == ';') i++; } int memo[64]; for (int x = 0; x < 64; x++) memo[x] = -1; return lc_paths_dfs(0, n, g, deg, memo);
}
```
