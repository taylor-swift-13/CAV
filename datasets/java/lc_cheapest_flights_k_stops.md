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

```java
class LcCheapestFlightsKStops {
    public static int lc_cheapest_flights_k_stops(int n, String flights, int src, int dst, int k) {
        String[] rows = flights.split(";"); int[][] e = new int[rows.length][3]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(","); for (int j = 0; j < 3; j++) e[i][j] = Integer.parseInt(p[j]); } int[] dist = new int[n]; java.util.Arrays.fill(dist, 1000000000); dist[src] = 0; for (int step = 0; step <= k; step++) { int[] next = dist.clone(); for (int[] f : e) if (dist[f[0]] != 1000000000 && dist[f[0]] + f[2] < next[f[1]]) next[f[1]] = dist[f[0]] + f[2]; dist = next; } return dist[dst] == 1000000000 ? -1 : dist[dst];
    }
}
```
