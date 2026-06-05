# LC Number Of Provinces Rows

## Problem

Return the number of connected components in an adjacency matrix.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.
- The matrix is square.

## Source

- Source: LeetCode problem `number-of-provinces`.
- URL: https://leetcode.com/problems/number-of-provinces/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_number_of_provinces_rows(const char *rows) {
    char g[128][128]; int n = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] == '0' || rows[i] == '1') { g[n][c] = rows[i++]; c++; } if (cols == 0) cols = c; n++; if (rows[i] == ';') i++; }
    int seen[128] = {0}, stack[128], ans = 0; for (int s = 0; s < n; s++) if (!seen[s]) { ans++; int top = 0; stack[top] = s; top++; seen[s] = 1; while (top > 0) { int v = stack[--top]; for (int to = 0; to < cols; to++) if (g[v][to] == '1' && !seen[to]) { seen[to] = 1; stack[top] = to; top++; } } } return ans;
}
```
