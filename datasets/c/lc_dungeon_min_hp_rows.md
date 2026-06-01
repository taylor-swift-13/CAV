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

```c
int lc_dungeon_min_hp_rows(const char *rows) {
    int a[64][64], r = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] != '\0' && rows[i] != ';') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[r][c++] = sign * v; if (rows[i] == ',') i++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int dp[65][65]; for (int x = 0; x <= r; x++) for (int y = 0; y <= cols; y++) dp[x][y] = 1000000000; dp[r][cols - 1] = 1; dp[r - 1][cols] = 1; for (int x = r - 1; x >= 0; x--) for (int y = cols - 1; y >= 0; y--) { int need = (dp[x + 1][y] < dp[x][y + 1] ? dp[x + 1][y] : dp[x][y + 1]) - a[x][y]; dp[x][y] = need <= 1 ? 1 : need; } return dp[0][0];
}
```
