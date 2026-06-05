# LC Eventual Safe Nodes Count

## Problem

Return how many nodes are eventually safe in a directed graph.

## Requirements

- `edges` is semicolon-separated `from,to` pairs.
- Nodes with no outgoing edges are terminal and safe.

## Source

- Source: LeetCode problem `find-eventual-safe-states`.
- URL: https://leetcode.com/problems/find-eventual-safe-states/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcEventualSafeNodesCount {
    public static int lc_eventual_safe_nodes_count(int n, String edges) {
        int[][] rev = new int[n][n]; int[] revn = new int[n], out = new int[n]; for (String e : edges.split(";")) { String[] p = e.split(","); int a = Integer.parseInt(p[0]), b = Integer.parseInt(p[1]); rev[b][revn[b]++] = a; out[a]++; } int[] q = new int[n]; int h = 0, t = 0; for (int v = 0; v < n; v++) if (out[v] == 0) q[t++] = v; while (h < t) { int v = q[h++]; for (int k = 0; k < revn[v]; k++) if (--out[rev[v][k]] == 0) q[t++] = rev[v][k]; } return t;
    }
}
```
