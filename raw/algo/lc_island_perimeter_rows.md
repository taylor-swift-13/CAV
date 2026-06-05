# LC Island Perimeter Rows

## Problem

Return the perimeter of land cells in a semicolon-separated 0/1 grid.

## Requirements

- Rows contain only `0` and `1`.
- All rows have equal positive length.

## Source

- Source: LeetCode problem `island-perimeter`.
- URL: https://leetcode.com/problems/island-perimeter/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_island_perimeter_rows(const char *rows) {
    char g[64][64]; int r = 0, c = 0, cols = 0, i = 0;
    while (rows[i] != '\0') { c = 0; while (rows[i] == '0' || rows[i] == '1') { g[r][c] = rows[i++]; c++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int ans = 0; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (g[x][y] == '1') { ans += 4; if (x > 0 && g[x - 1][y] == '1') ans -= 2; if (y > 0 && g[x][y - 1] == '1') ans -= 2; }
    return ans;
}
```
