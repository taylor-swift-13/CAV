# LC Find If Path Exists Graph Bool

## Problem

Return true if there is a path from `source` to `destination` in an undirected graph.

## Requirements

- Edges are encoded as `u,v;...`.
- Vertices are numbered from `0` to `n-1`.

## Source

- Source: LeetCode problem `find-if-path-exists-in-graph`.
- URL: https://leetcode.com/problems/find-if-path-exists-in-graph/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_valid_path_graph_bool(n: i32, edges: &str, source: i32, destination: i32) -> bool {
    let nn = n as usize; let mut g = vec![vec![false; nn]; nn]; if !edges.is_empty() { for e in edges.split(';') { let p: Vec<usize> = e.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); g[p[0]][p[1]] = true; g[p[1]][p[0]] = true; } } let mut seen = vec![false; nn]; let mut q = vec![source as usize]; let mut head = 0usize; seen[source as usize] = true; while head < q.len() { let v = q[head]; head += 1; if v == destination as usize { return true; } let mut to = 0usize; while to < nn { if g[v][to] && !seen[to] { seen[to] = true; q.push(to); } to += 1; } } false
}
```
