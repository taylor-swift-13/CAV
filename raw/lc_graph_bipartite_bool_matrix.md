# LC Is Graph Bipartite Bool Matrix

## Problem

Return true if an undirected graph is bipartite.

## Requirements

- The graph is encoded as a square adjacency matrix with semicolon-separated `0`/`1` rows.

## Source

- Source: LeetCode problem `is-graph-bipartite`.
- URL: https://leetcode.com/problems/is-graph-bipartite/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_graph_bipartite_bool_matrix(const char *rows) {
    char g[128][128]; int n = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] == '0' || rows[i] == '1') { g[n][c] = rows[i++]; c++; } if (cols == 0) cols = c; n++; if (rows[i] == ';') i++; }
    int color[128]; for (int x = 0; x < n; x++) color[x] = -1; int q[128]; for (int s = 0; s < n; s++) if (color[s] < 0) { int head = 0, tail = 0; q[tail] = s; tail++; color[s] = 0; while (head < tail) { int v = q[head++]; for (int to = 0; to < cols; to++) if (g[v][to] == '1') { if (color[to] < 0) { color[to] = 1 - color[v]; q[tail] = to; tail++; } else if (color[to] == color[v]) return 0; } } } return 1;
}
```
