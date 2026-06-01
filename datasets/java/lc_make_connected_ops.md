# LC Network Connected Operations

## Problem

Return the minimum cable moves needed to connect all computers, or `-1` if impossible.

## Requirements

- Connections are encoded as `u,v;...`.
- Computers are numbered from `0` to `n-1`.

## Source

- Source: LeetCode problem `number-of-operations-to-make-network-connected`.
- URL: https://leetcode.com/problems/number-of-operations-to-make-network-connected/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMakeConnectedOps {
    public static int lc_make_connected_ops(int n, String connections) {
        boolean[][] g = new boolean[n][n]; int edges = 0; if (!connections.isEmpty()) for (String e : connections.split(";")) { String[] p = e.split(","); int a = Integer.parseInt(p[0]), b = Integer.parseInt(p[1]); g[a][b] = true; g[b][a] = true; edges++; } if (edges < n - 1) return -1; boolean[] seen = new boolean[n]; int comps = 0; int[] q = new int[n]; for (int s = 0; s < n; s++) if (!seen[s]) { comps++; int head = 0, tail = 0; q[tail++] = s; seen[s] = true; while (head < tail) { int v = q[head++]; for (int to = 0; to < n; to++) if (g[v][to] && !seen[to]) { seen[to] = true; q[tail++] = to; } } } return comps - 1;
    }
}
```
