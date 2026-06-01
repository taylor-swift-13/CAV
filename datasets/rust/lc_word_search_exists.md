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

```rust
pub fn lc_word_search_exists(rows: &str, word: &str) -> bool {
    fn dfs(g: &mut Vec<Vec<u8>>, x: i32, y: i32, w: &[u8], p: usize) -> bool { if p == w.len() { return true; } if x < 0 || y < 0 || x >= g.len() as i32 || y >= g[0].len() as i32 || g[x as usize][y as usize] != w[p] { return false; } let old = g[x as usize][y as usize]; g[x as usize][y as usize] = b'#'; let ok = dfs(g,x+1,y,w,p+1) || dfs(g,x-1,y,w,p+1) || dfs(g,x,y+1,w,p+1) || dfs(g,x,y-1,w,p+1); g[x as usize][y as usize] = old; ok }
    let mut g: Vec<Vec<u8>> = rows.split(';').map(|s| s.as_bytes().to_vec()).collect(); let w = word.as_bytes(); let mut i = 0usize; while i < g.len() { let mut j = 0usize; while j < g[0].len() { if dfs(&mut g, i as i32, j as i32, w, 0) { return true; } j += 1; } i += 1; } false
}
```
