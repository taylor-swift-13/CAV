# LC Cheapest Flights Within K Stops

## Problem

Return the cheapest price from `src` to `dst` using at most `k` stops, or `-1`.

## Requirements

- Flights are encoded as `from,to,price;...`.
- Cities are numbered from `0` to `n-1`.

## Source

- Source: LeetCode problem `cheapest-flights-within-k-stops`.
- URL: https://leetcode.com/problems/cheapest-flights-within-k-stops/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_cheapest_flights_k_stops(int n, const char *flights, int src, int dst, int k) {
    int u[512], v[512], w[512], m = 0, i = 0; while (flights[i] != '\0') { int vals[3]; for (int t = 0; t < 3; t++) { int x = 0; while (flights[i] >= '0' && flights[i] <= '9') { x = x * 10 + (flights[i] - '0'); i++; } vals[t] = x; if (flights[i] == ',') i++; } u[m] = vals[0]; v[m] = vals[1]; w[m++] = vals[2]; if (flights[i] == ';') i++; }
    int dist[128], next[128]; for (int x = 0; x < n; x++) dist[x] = 1000000000; dist[src] = 0; for (int step = 0; step <= k; step++) { for (int x = 0; x < n; x++) next[x] = dist[x]; for (int e = 0; e < m; e++) if (dist[u[e]] != 1000000000 && dist[u[e]] + w[e] < next[v[e]]) next[v[e]] = dist[u[e]] + w[e]; for (int x = 0; x < n; x++) dist[x] = next[x]; } return dist[dst] == 1000000000 ? -1 : dist[dst];
}
```
