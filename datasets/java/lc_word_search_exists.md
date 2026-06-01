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

```java
class LcWordSearchExists {
    static boolean dfs(char[][] g, int x, int y, String w, int p) { if (p == w.length()) return true; if (x < 0 || x >= g.length || y < 0 || y >= g[0].length || g[x][y] != w.charAt(p)) return false; char old = g[x][y]; g[x][y] = '#'; boolean ok = dfs(g,x+1,y,w,p+1) || dfs(g,x-1,y,w,p+1) || dfs(g,x,y+1,w,p+1) || dfs(g,x,y-1,w,p+1); g[x][y] = old; return ok; }
    public static boolean lc_word_search_exists(String rows, String word) {
        String[] rs = rows.split(";"); char[][] g = new char[rs.length][rs[0].length()]; for (int i = 0; i < rs.length; i++) g[i] = rs[i].toCharArray();
        for (int i = 0; i < g.length; i++) for (int j = 0; j < g[0].length; j++) if (dfs(g, i, j, word, 0)) return true; return false;
    }
}
```
