# LC Minimum Height Trees Root Count

## Problem

Return the number of roots that produce minimum-height trees.

## Requirements

- `edges` is semicolon-separated undirected `u,v` pairs.
- The graph is a tree with `n` nodes.

## Source

- Source: LeetCode problem `minimum-height-trees`.
- URL: https://leetcode.com/problems/minimum-height-trees/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_height_trees_root_count(n: i32, edges: &str) -> i32 {
    let nn = n as usize; let mut g = vec![Vec::<usize>::new(); nn]; let mut deg = vec![0; nn]; for e in edges.split(';') { let p: Vec<usize> = e.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); g[p[0]].push(p[1]); g[p[1]].push(p[0]); deg[p[0]] += 1; deg[p[1]] += 1; } let mut left = nn; let mut leaves: Vec<usize> = (0..nn).filter(|&v| deg[v] <= 1).collect(); while left > 2 { left -= leaves.len(); let mut next = Vec::new(); for &v in &leaves { for &to in &g[v] { deg[to] -= 1; if deg[to] == 1 { next.push(to); } } } leaves = next; } left as i32
}
```
