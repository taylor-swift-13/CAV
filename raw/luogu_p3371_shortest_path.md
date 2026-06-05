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

```c
int luogu_p3371_shortest_path(int n, const char *edges, int s, int target) {
    int u[1024], v[1024], w[1024], m = 0, i = 0; while (edges[i] != '\0') { int vals[3]; for (int k = 0; k < 3; k++) { int x = 0; while (edges[i] >= '0' && edges[i] <= '9') { x = x * 10 + (edges[i] - '0'); i++; } vals[k] = x; if (edges[i] == ',') i++; } u[m] = vals[0]; v[m] = vals[1]; w[m] = vals[2]; m++; if (edges[i] == ';') i++; }
    int dist[256], used[256] = {0}; for (int x = 1; x <= n; x++) dist[x] = 1000000000; dist[s] = 0; for (int step = 0; step < n; step++) { int node = -1; for (int x = 1; x <= n; x++) if (!used[x] && (node == -1 || dist[x] < dist[node])) node = x; if (node == -1 || dist[node] == 1000000000) break; used[node] = 1; for (int e = 0; e < m; e++) if (u[e] == node && dist[node] + w[e] < dist[v[e]]) dist[v[e]] = dist[node] + w[e]; } return dist[target] == 1000000000 ? -1 : dist[target];
}
```
