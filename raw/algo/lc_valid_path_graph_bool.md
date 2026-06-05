# LC Find If Path Exists Graph Bool

## Problem

Return true if there is a path from `source` to `destination` in an undirected graph.

## Requirements

- Edges are encoded as `u,v;...`.
- Vertices are numbered from `0` to `n-1`.

## Source

- Source: LeetCode problem `find-if-path-exists-in-graph`.
- URL: https://leetcode.com/problems/find-if-path-exists-in-graph/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_valid_path_graph_bool(int n, const char *edges, int source, int destination) {
    int g[128][128] = {{0}}, i = 0; while (edges[i] != '\0') { int a = 0, b = 0; while (edges[i] >= '0' && edges[i] <= '9') { a = a * 10 + (edges[i] - '0'); i++; } if (edges[i] == ',') i++; while (edges[i] >= '0' && edges[i] <= '9') { b = b * 10 + (edges[i] - '0'); i++; } g[a][b] = 1; g[b][a] = 1; if (edges[i] == ';') i++; }
    int seen[128] = {0}, q[128], head = 0, tail = 0; q[tail] = source; tail++; seen[source] = 1; while (head < tail) { int v = q[head++]; if (v == destination) return 1; for (int to = 0; to < n; to++) if (g[v][to] && !seen[to]) { seen[to] = 1; q[tail] = to; tail++; } } return 0;
}
```
