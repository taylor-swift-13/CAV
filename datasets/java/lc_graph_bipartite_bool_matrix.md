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

```java
class LcGraphBipartiteBoolMatrix {
    public static boolean lc_graph_bipartite_bool_matrix(String rows) {
        String[] rs = rows.split(";"); int n = rs.length; int[] color = new int[n]; java.util.Arrays.fill(color, -1); int[] q = new int[n]; for (int s = 0; s < n; s++) if (color[s] < 0) { int head = 0, tail = 0; q[tail++] = s; color[s] = 0; while (head < tail) { int v = q[head++]; for (int to = 0; to < n; to++) if (rs[v].charAt(to) == '1') { if (color[to] < 0) { color[to] = 1 - color[v]; q[tail++] = to; } else if (color[to] == color[v]) return false; } } } return true;
    }
}
```
