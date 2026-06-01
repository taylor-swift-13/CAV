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

```java
class LcValidPathGraphBool {
    public static boolean lc_valid_path_graph_bool(int n, String edges, int source, int destination) {
        boolean[][] g = new boolean[n][n]; if (!edges.isEmpty()) for (String e : edges.split(";")) { String[] p = e.split(","); int a = Integer.parseInt(p[0]), b = Integer.parseInt(p[1]); g[a][b] = true; g[b][a] = true; } boolean[] seen = new boolean[n]; int[] q = new int[n]; int head = 0, tail = 0; q[tail++] = source; seen[source] = true; while (head < tail) { int v = q[head++]; if (v == destination) return true; for (int to = 0; to < n; to++) if (g[v][to] && !seen[to]) { seen[to] = true; q[tail++] = to; } } return false;
    }
}
```
