# LC All Paths Source Target Count

## Problem

Return how many directed paths go from node `0` to node `n-1` in a DAG.

## Requirements

- Adjacency lists are semicolon-separated.
- Neighbors inside a list are comma-separated; `-` means no outgoing edges.

## Source

- Source: LeetCode problem `all-paths-from-source-to-target`.
- URL: https://leetcode.com/problems/all-paths-from-source-to-target/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_all_paths_source_target_count(graph: &str) -> i32 {
    fn dfs(v: usize, n: usize, g: &Vec<Vec<usize>>, memo: &mut Vec<i32>) -> i32 { if v == n - 1 { return 1; } if memo[v] >= 0 { return memo[v]; } let mut ans = 0; for &to in &g[v] { ans += dfs(to, n, g, memo); } memo[v] = ans; ans } let g: Vec<Vec<usize>> = graph.split(';').map(|r| if r == "-" { Vec::new() } else { r.split(',').map(|x| x.parse::<usize>().unwrap()).collect() }).collect(); let mut memo = vec![-1; g.len()]; dfs(0, g.len(), &g, &mut memo)
}
```
