# Luogu P3366 MST Weight

## Problem

Return the total weight of a minimum spanning tree, or `-1` if the graph is disconnected.

## Requirements

- Undirected weighted edges are encoded as `u,v,w;...`.
- Vertices are numbered from `1` to `n`.

## Source

- Source: Luogu problem `P3366`.
- URL: https://www.luogu.com.cn/problem/P3366
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP3366MstWeight {
    public static int luogu_p3366_mst_weight(int n, String edges) {
        String[] rows = edges.split(";"); int[][] e = new int[rows.length][3]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(","); for (int j = 0; j < 3; j++) e[i][j] = Integer.parseInt(p[j]); } java.util.Arrays.sort(e, (a, b) -> Integer.compare(a[2], b[2])); int[] parent = new int[n + 1]; for (int i = 1; i <= n; i++) parent[i] = i; int total = 0, used = 0; for (int[] edge : e) { int a = edge[0], b = edge[1]; while (parent[a] != a) a = parent[a]; while (parent[b] != b) b = parent[b]; if (a != b) { parent[a] = b; total += edge[2]; used++; } } return used == n - 1 ? total : -1;
    }
}
```
