# LC Swim In Rising Water Time Rows

## Problem

Return the minimum time needed to reach the bottom-right cell.

## Requirements

- Grid values are encoded as semicolon-separated comma rows.
- You may move 4-directionally through cells whose value is at most the current time.

## Source

- Source: LeetCode problem `swim-in-rising-water`.
- URL: https://leetcode.com/problems/swim-in-rising-water/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcSwimRisingWaterTimeRows {
    public static int lc_swim_rising_water_time_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].split(",").length; int[][] a = new int[r][c]; for (int i = 0; i < r; i++) { String[] p = rs[i].split(","); for (int j = 0; j < c; j++) a[i][j] = Integer.parseInt(p[j]); } int total = r * c; int[] dist = new int[total]; boolean[] used = new boolean[total]; java.util.Arrays.fill(dist, 1000000000); dist[0] = a[0][0]; int[] dx = {1,-1,0,0}, dy = {0,0,1,-1}; for (int step = 0; step < total; step++) { int node = -1; for (int i = 0; i < total; i++) if (!used[i] && (node < 0 || dist[i] < dist[node])) node = i; if (node == total - 1) break; used[node] = true; int x = node / c, y = node % c; for (int d = 0; d < 4; d++) { int nx = x + dx[d], ny = y + dy[d]; if (nx >= 0 && nx < r && ny >= 0 && ny < c) { int ni = nx * c + ny; int nd = Math.max(dist[node], a[nx][ny]); if (nd < dist[ni]) dist[ni] = nd; } } } return dist[total - 1];
    }
}
```
