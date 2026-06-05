# LC Network Delay Time

## Problem

Return the time for all nodes to receive a signal, or `-1`.

## Requirements

- Directed weighted edges are encoded as `u,v,w;...`.
- Nodes are numbered from `1` to `n`.

## Source

- Source: LeetCode problem `network-delay-time`.
- URL: https://leetcode.com/problems/network-delay-time/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_network_delay_time(const char *times, int n, int k) {
    int u[512], v[512], w[512], m = 0, i = 0; while (times[i] != '\0') { int vals[3]; for (int t = 0; t < 3; t++) { int x = 0; while (times[i] >= '0' && times[i] <= '9') { x = x * 10 + (times[i] - '0'); i++; } vals[t] = x; if (times[i] == ',') i++; } u[m] = vals[0]; v[m] = vals[1]; w[m] = vals[2]; m++; if (times[i] == ';') i++; }
    int dist[128], used[128] = {0}; for (int x = 1; x <= n; x++) dist[x] = 1000000000; dist[k] = 0; for (int step = 0; step < n; step++) { int node = -1; for (int x = 1; x <= n; x++) if (!used[x] && (node == -1 || dist[x] < dist[node])) node = x; if (node == -1 || dist[node] == 1000000000) break; used[node] = 1; for (int e = 0; e < m; e++) if (u[e] == node && dist[node] + w[e] < dist[v[e]]) dist[v[e]] = dist[node] + w[e]; }
    int ans = 0; for (int x = 1; x <= n; x++) { if (dist[x] == 1000000000) return -1; if (dist[x] > ans) ans = dist[x]; } return ans;
}
```
