# LC Min Cost Connect Points

## Problem

Return the minimum total Manhattan distance needed to connect all points.

## Requirements

- Points are encoded as `x,y;...`.
- This is the MST objective from the original problem.

## Source

- Source: LeetCode problem `min-cost-to-connect-all-points`.
- URL: https://leetcode.com/problems/min-cost-to-connect-all-points/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMinCostConnectPoints {
    public static int lc_min_cost_connect_points(String points) {
        String[] rows = points.split(";"); int n = rows.length; int[] x = new int[n], y = new int[n]; for (int i = 0; i < n; i++) { String[] p = rows[i].split(","); x[i] = Integer.parseInt(p[0]); y[i] = Integer.parseInt(p[1]); } boolean[] used = new boolean[n]; int[] dist = new int[n]; java.util.Arrays.fill(dist, 1000000000); dist[0] = 0; int total = 0; for (int step = 0; step < n; step++) { int v = -1; for (int i = 0; i < n; i++) if (!used[i] && (v < 0 || dist[i] < dist[v])) v = i; used[v] = true; total += dist[v]; for (int to = 0; to < n; to++) { int w = Math.abs(x[v] - x[to]) + Math.abs(y[v] - y[to]); if (!used[to] && w < dist[to]) dist[to] = w; } } return total;
    }
}
```
