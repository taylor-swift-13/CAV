# LC Is Graph Bipartite Bool Matrix

## Problem

Return true if an undirected graph is bipartite.

## Requirements

- The graph is encoded as a square adjacency matrix with semicolon-separated `0`/`1` rows.

## Source

- Source: LeetCode problem `is-graph-bipartite`.
- URL: https://leetcode.com/problems/is-graph-bipartite/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_graph_bipartite_bool_matrix(rows: &str) -> bool {
    let g: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let n = g.len(); let mut color = vec![-1; n]; let mut s = 0usize; while s < n { if color[s] < 0 { let mut q = vec![s]; let mut head = 0usize; color[s] = 0; while head < q.len() { let v = q[head]; head += 1; let mut to = 0usize; while to < n { if g[v][to] == b'1' { if color[to] < 0 { color[to] = 1 - color[v]; q.push(to); } else if color[to] == color[v] { return false; } } to += 1; } } } s += 1; } true
}
```
