# Luogu P3371 Shortest Path

## Problem

Return the shortest-path distance from source `s` to `target`, or `-1` if unreachable.

## Requirements

- Directed weighted edges are encoded as `u,v,w;...`.
- Vertices are numbered from `1` to `n`.

## Source

- Source: Luogu problem `P3371`.
- URL: https://www.luogu.com.cn/problem/P3371
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP3371ShortestPath {
    public static int luogu_p3371_shortest_path(int n, String edges, int s, int target) {
        String[] rows = edges.split(";"); int[][] e = new int[rows.length][3]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(","); for (int j = 0; j < 3; j++) e[i][j] = Integer.parseInt(p[j]); } int[] dist = new int[n + 1]; boolean[] used = new boolean[n + 1]; java.util.Arrays.fill(dist, 1000000000); dist[s] = 0; for (int step = 0; step < n; step++) { int node = -1; for (int i = 1; i <= n; i++) if (!used[i] && (node == -1 || dist[i] < dist[node])) node = i; if (node == -1 || dist[node] == 1000000000) break; used[node] = true; for (int[] edge : e) if (edge[0] == node && dist[node] + edge[2] < dist[edge[1]]) dist[edge[1]] = dist[node] + edge[2]; } return dist[target] == 1000000000 ? -1 : dist[target];
    }
}
```
