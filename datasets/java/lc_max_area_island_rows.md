# LC Max Area Of Island Rows

## Problem

Return the maximum area of a 4-directionally connected island in a 0/1 grid.

## Requirements

- Rows are semicolon-separated.
- Rows contain only `0` and `1`.

## Source

- Source: LeetCode problem `max-area-of-island`.
- URL: https://leetcode.com/problems/max-area-of-island/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMaxAreaIslandRows {
    public static int lc_max_area_island_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].length(), best = 0; char[][] g = new char[r][c]; for (int i = 0; i < r; i++) g[i] = rs[i].toCharArray(); int[] sx = new int[r * c], sy = new int[r * c], dx = {1,-1,0,0}, dy = {0,0,1,-1};
        for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (g[i][j] == '1') { int area = 0, top = 0; sx[top] = i; sy[top++] = j; g[i][j] = '0'; while (top > 0) { top--; int x = sx[top], y = sy[top]; area++; for (int k = 0; k < 4; k++) { int nx = x + dx[k], ny = y + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < c && g[nx][ny] == '1') { g[nx][ny] = '0'; sx[top] = nx; sy[top++] = ny; } } } if (area > best) best = area; } return best;
    }
}
```
