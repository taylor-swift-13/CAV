# LC Maximal Rectangle Area Rows

## Problem

Return the area of the largest all-1 rectangle in a semicolon-separated binary matrix.

## Requirements

- Rows contain only `0` and `1`.
- All rows have equal positive length.
- The empty string returns `0`.

## Source

- Source: LeetCode problem `maximal-rectangle`.
- URL: https://leetcode.com/problems/maximal-rectangle/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_maximal_rectangle_area_rows(const char *rows) {
    if (rows[0] == '\0') return 0;
    char g[64][64]; int r = 0, c = 0, cols = 0, i = 0;
    while (rows[i] != '\0') { c = 0; while (rows[i] == '0' || rows[i] == '1') { g[r][c] = rows[i++]; c++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int h[64] = {0}, best = 0, st[65];
    for (int x = 0; x < r; x++) { for (int y = 0; y < cols; y++) h[y] = g[x][y] == '1' ? h[y] + 1 : 0; int top = 0; for (int y = 0; y <= cols; y++) { int cur = y == cols ? 0 : h[y]; while (top > 0 && h[st[top - 1]] > cur) { int height = h[st[--top]]; int left = top == 0 ? -1 : st[top - 1]; int area = height * (y - left - 1); if (area > best) best = area; } st[top] = y; top++; } }
    return best;
}
```
