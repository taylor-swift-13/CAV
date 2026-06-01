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

```c
int luogu_p3366_mst_weight(int n, const char *edges) {
    int u[1024], v[1024], w[1024], m = 0, i = 0; while (edges[i] != '\0') { int vals[3]; for (int k = 0; k < 3; k++) { int x = 0; while (edges[i] >= '0' && edges[i] <= '9') { x = x * 10 + edges[i] - '0'; i++; } vals[k] = x; if (edges[i] == ',') i++; } u[m] = vals[0]; v[m] = vals[1]; w[m++] = vals[2]; if (edges[i] == ';') i++; }
    for (int a = 0; a < m; a++) for (int b = a + 1; b < m; b++) if (w[b] < w[a]) { int tu = u[a], tv = v[a], tw = w[a]; u[a] = u[b]; v[a] = v[b]; w[a] = w[b]; u[b] = tu; v[b] = tv; w[b] = tw; }
    int parent[256]; for (int x = 1; x <= n; x++) parent[x] = x; int total = 0, used = 0; for (int e = 0; e < m; e++) { int a = u[e], b = v[e]; while (parent[a] != a) a = parent[a]; while (parent[b] != b) b = parent[b]; if (a != b) { parent[a] = b; total += w[e]; used++; } } return used == n - 1 ? total : -1;
}
```
