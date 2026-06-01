# LC Number Of Islands Rows

## Problem

Count 4-directionally connected islands of `1` cells in a semicolon-separated binary grid.

## Requirements

- Rows contain only `0` and `1`.
- All rows have equal positive length.
- The empty string returns `0`.

## Source

- Source: LeetCode problem `number-of-islands`.
- URL: https://leetcode.com/problems/number-of-islands/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcNumberOfIslandsRows {
    public static int lc_number_of_islands_rows(String rows) {
        if (rows.isEmpty()) return 0; String[] rs = rows.split(";"); int r = rs.length, c = rs[0].length(); char[][] g = new char[r][c]; for (int i = 0; i < r; i++) g[i] = rs[i].toCharArray();
        int ans = 0; int[] sx = new int[r * c], sy = new int[r * c]; int[] dx = {1,-1,0,0}, dy = {0,0,1,-1};
        for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (g[i][j] == '1') { ans++; int top = 0; sx[top] = i; sy[top++] = j; g[i][j] = '0'; while (top > 0) { top--; int x = sx[top], y = sy[top]; for (int k = 0; k < 4; k++) { int nx = x + dx[k], ny = y + dy[k]; if (nx >= 0 && nx < r && ny >= 0 && ny < c && g[nx][ny] == '1') { g[nx][ny] = '0'; sx[top] = nx; sy[top++] = ny; } } } }
        return ans;
    }
}
```
