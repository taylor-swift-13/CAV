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

```c
int lc_min_cost_connect_points(const char *points) {
    int x[128], y[128], n = 0, i = 0; while (points[i] != '\0') { int vals[2]; for (int k = 0; k < 2; k++) { int sign = 1, v = 0; if (points[i] == '-') { sign = -1; i++; } while (points[i] >= '0' && points[i] <= '9') { v = v * 10 + (points[i] - '0'); i++; } vals[k] = sign * v; if (points[i] == ',') i++; } x[n] = vals[0]; y[n++] = vals[1]; if (points[i] == ';') i++; }
    int used[128] = {0}, dist[128]; for (int a = 0; a < n; a++) dist[a] = 1000000000; dist[0] = 0; int total = 0; for (int step = 0; step < n; step++) { int v = -1; for (int a = 0; a < n; a++) if (!used[a] && (v < 0 || dist[a] < dist[v])) v = a; used[v] = 1; total += dist[v]; for (int to = 0; to < n; to++) { int dx = x[v] > x[to] ? x[v] - x[to] : x[to] - x[v]; int dy = y[v] > y[to] ? y[v] - y[to] : y[to] - y[v]; int w = dx + dy; if (!used[to] && w < dist[to]) dist[to] = w; } } return total;
}
```
