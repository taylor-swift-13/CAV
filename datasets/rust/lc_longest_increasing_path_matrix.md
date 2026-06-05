# LC Longest Increasing Path Matrix

## Problem

Return the length of the longest strictly increasing 4-directional path in a matrix.

## Requirements

- Rows are semicolon-separated comma lists of signed integers.

## Source

- Source: LeetCode problem `longest-increasing-path-in-a-matrix`.
- URL: https://leetcode.com/problems/longest-increasing-path-in-a-matrix/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_longest_increasing_path_matrix(rows: &str) -> i32 {
    fn dfs(x: usize, y: usize, a: &Vec<Vec<i32>>, memo: &mut Vec<Vec<i32>>) -> i32 { if memo[x][y] != 0 { return memo[x][y]; } let dirs = [(1i32,0i32),(-1,0),(0,1),(0,-1)]; let mut best = 1; for &(dx,dy) in dirs.iter() { let nx = x as i32 + dx; let ny = y as i32 + dy; if nx >= 0 && nx < a.len() as i32 && ny >= 0 && ny < a[0].len() as i32 && a[nx as usize][ny as usize] > a[x][y] { let cand = 1 + dfs(nx as usize, ny as usize, a, memo); if cand > best { best = cand; } } } memo[x][y] = best; best }
    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let mut memo = vec![vec![0; a[0].len()]; a.len()]; let mut ans = 0; let mut i = 0usize; while i < a.len() { let mut j = 0usize; while j < a[0].len() { let v = dfs(i, j, &a, &mut memo); if v > ans { ans = v; } j += 1; } i += 1; } ans
}
```
