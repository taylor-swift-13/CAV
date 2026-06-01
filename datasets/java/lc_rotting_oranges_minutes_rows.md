# LC Rotting Oranges Minutes Rows

## Problem

Return the minimum minutes until no fresh orange remains, or `-1` if impossible.

## Requirements

- Rows are semicolon-separated strings of digits.
- `0` is empty, `1` fresh, and `2` rotten.

## Source

- Source: LeetCode problem `rotting-oranges`.
- URL: https://leetcode.com/problems/rotting-oranges/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcRottingOrangesMinutesRows {
    public static int lc_rotting_oranges_minutes_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].length(), fresh = 0, head = 0, tail = 0, minutes = 0; char[][] g = new char[r][c]; int[] qx = new int[r * c], qy = new int[r * c], qt = new int[r * c]; for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) { g[i][j] = rs[i].charAt(j); if (g[i][j] == '1') fresh++; if (g[i][j] == '2') { qx[tail] = i; qy[tail] = j; qt[tail++] = 0; } } int[] dx = {1,-1,0,0}, dy = {0,0,1,-1}; while (head < tail) { int x = qx[head], y = qy[head], t = qt[head++]; minutes = Math.max(minutes, t); for (int d = 0; d < 4; d++) { int nx = x + dx[d], ny = y + dy[d]; if (nx >= 0 && nx < r && ny >= 0 && ny < c && g[nx][ny] == '1') { g[nx][ny] = '2'; fresh--; qx[tail] = nx; qy[tail] = ny; qt[tail++] = t + 1; } } } return fresh == 0 ? minutes : -1;
    }
}
```
