# LC Count Servers That Communicate Rows

## Problem

Return how many servers can communicate with at least one other server in the same row or column.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.

## Source

- Source: LeetCode problem `count-servers-that-communicate`.
- URL: https://leetcode.com/problems/count-servers-that-communicate/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_count_servers_rows(const char *rows) {
    char g[64][64]; int r = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] == '0' || rows[i] == '1') g[r][c++] = rows[i++]; if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; } int row[64] = {0}, col[64] = {0}; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (g[x][y] == '1') { row[x]++; col[y]++; } int ans = 0; for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (g[x][y] == '1' && (row[x] > 1 || col[y] > 1)) ans++; return ans;
}
```
