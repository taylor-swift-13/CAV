# LC Word Search Exists

## Problem

Return true if `word` can be formed by adjacent cells in a semicolon-separated board.

## Requirements

- Adjacent means up/down/left/right.
- Each cell can be used at most once in a path.
- Rows have equal length.

## Source

- Source: LeetCode problem `word-search`.
- URL: https://leetcode.com/problems/word-search/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
static int lc_word_search_dfs(char g[16][16], int r, int c, int x, int y, const char *w, int p) { if (w[p] == '\0') return 1; if (x < 0 || x >= r || y < 0 || y >= c || g[x][y] != w[p]) return 0; char old = g[x][y]; g[x][y] = '#'; int ok = lc_word_search_dfs(g,r,c,x+1,y,w,p+1) || lc_word_search_dfs(g,r,c,x-1,y,w,p+1) || lc_word_search_dfs(g,r,c,x,y+1,w,p+1) || lc_word_search_dfs(g,r,c,x,y-1,w,p+1); g[x][y] = old; return ok; }
int lc_word_search_exists(const char *rows, const char *word) {
    char g[16][16]; int r = 0, c = 0, cols = 0, i = 0;
    while (rows[i] != '\0') { c = 0; while (rows[i] != '\0' && rows[i] != ';') { g[r][c] = rows[i++]; c++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    for (int x = 0; x < r; x++) for (int y = 0; y < cols; y++) if (lc_word_search_dfs(g, r, cols, x, y, word, 0)) return 1;
    return 0;
}
```
