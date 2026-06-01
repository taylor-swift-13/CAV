# LC As Far From Land As Possible Rows

## Problem

Return the maximum Manhattan distance from any water cell to nearest land, or `-1` if no answer exists.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.
- `1` is land and `0` is water.

## Source

- Source: LeetCode problem `as-far-from-land-as-possible`.
- URL: https://leetcode.com/problems/as-far-from-land-as-possible/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMaxDistanceFromLandRows {
    public static int lc_max_distance_from_land_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].length(), head = 0, tail = 0, water = 0; char[][] g = new char[r][c]; int[] qx = new int[r * c], qy = new int[r * c], qd = new int[r * c]; for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) { g[i][j] = rs[i].charAt(j); if (g[i][j] == '1') { qx[tail] = i; qy[tail] = j; qd[tail++] = 0; } else water++; } if (tail == 0 || water == 0) return -1; int ans = 0; int[] dx = {1,-1,0,0}, dy = {0,0,1,-1}; while (head < tail) { int x = qx[head], y = qy[head], d = qd[head++]; ans = Math.max(ans, d); for (int k = 0; k < 4; k++) { int nx = x + dx[k], ny = y + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < c && g[nx][ny] == '0') { g[nx][ny] = '1'; qx[tail] = nx; qy[tail] = ny; qd[tail++] = d + 1; } } } return ans;
    }
}
```
