# LC Dungeon Game Minimum HP Rows

## Problem

Return the minimum initial health needed to rescue the princess.

## Requirements

- Dungeon rows are semicolon-separated comma lists of signed integers.
- Movement is only right or down.

## Source

- Source: LeetCode problem `dungeon-game`.
- URL: https://leetcode.com/problems/dungeon-game/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcDungeonMinHpRows {
    public static int lc_dungeon_min_hp_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].split(",").length; int[][] a = new int[r][c]; for (int i = 0; i < r; i++) { String[] p = rs[i].split(","); for (int j = 0; j < c; j++) a[i][j] = Integer.parseInt(p[j]); } int[][] dp = new int[r + 1][c + 1]; for (int i = 0; i <= r; i++) java.util.Arrays.fill(dp[i], 1000000000); dp[r][c - 1] = 1; dp[r - 1][c] = 1; for (int i = r - 1; i >= 0; i--) for (int j = c - 1; j >= 0; j--) { int need = Math.min(dp[i + 1][j], dp[i][j + 1]) - a[i][j]; dp[i][j] = need <= 1 ? 1 : need; } return dp[0][0];
    }
}
```
