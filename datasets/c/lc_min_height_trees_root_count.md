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

```c
int lc_min_height_trees_root_count(int n, const char *edges) {
    int g[128][128] = {{0}}, deg[128] = {0}, i = 0; while (edges[i] != '\0') { int a = 0, b = 0; while (edges[i] >= '0' && edges[i] <= '9') { a = a * 10 + edges[i] - '0'; i++; } if (edges[i] == ',') i++; while (edges[i] >= '0' && edges[i] <= '9') { b = b * 10 + edges[i] - '0'; i++; } g[a][b] = g[b][a] = 1; deg[a]++; deg[b]++; if (edges[i] == ';') i++; } int left = n, leaves[128], count = 0; for (int v = 0; v < n; v++) if (deg[v] <= 1) leaves[count++] = v; while (left > 2) { left -= count; int next[128], nc = 0; for (int k = 0; k < count; k++) { int v = leaves[k]; for (int to = 0; to < n; to++) if (g[v][to] && --deg[to] == 1) next[nc++] = to; } for (int k = 0; k < nc; k++) leaves[k] = next[k]; count = nc; } return left;
}
```
