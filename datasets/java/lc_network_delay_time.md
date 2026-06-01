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

```java
class LcNetworkDelayTime {
    public static int lc_network_delay_time(String times, int n, int k) {
        String[] rows = times.split(";"); int[][] e = new int[rows.length][3]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(","); for (int j = 0; j < 3; j++) e[i][j] = Integer.parseInt(p[j]); } int[] dist = new int[n + 1]; boolean[] used = new boolean[n + 1]; java.util.Arrays.fill(dist, 1000000000); dist[k] = 0; for (int step = 0; step < n; step++) { int node = -1; for (int i = 1; i <= n; i++) if (!used[i] && (node == -1 || dist[i] < dist[node])) node = i; if (node == -1 || dist[node] == 1000000000) break; used[node] = true; for (int[] edge : e) if (edge[0] == node && dist[node] + edge[2] < dist[edge[1]]) dist[edge[1]] = dist[node] + edge[2]; } int ans = 0; for (int i = 1; i <= n; i++) { if (dist[i] == 1000000000) return -1; ans = Math.max(ans, dist[i]); } return ans;
    }
}
```
