# LC Eventual Safe Nodes Count

## Problem

Return how many nodes are eventually safe in a directed graph.

## Requirements

- `edges` is semicolon-separated `from,to` pairs.
- Nodes with no outgoing edges are terminal and safe.

## Source

- Source: LeetCode problem `find-eventual-safe-states`.
- URL: https://leetcode.com/problems/find-eventual-safe-states/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_eventual_safe_nodes_count(n: i32, edges: &str) -> i32 {
    let nn = n as usize; let mut rev = vec![Vec::<usize>::new(); nn]; let mut out = vec![0; nn]; for e in edges.split(';') { let p: Vec<usize> = e.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); rev[p[1]].push(p[0]); out[p[0]] += 1; } let mut q = Vec::new(); for v in 0..nn { if out[v] == 0 { q.push(v); } } let mut h = 0usize; while h < q.len() { let v = q[h]; h += 1; for &pre in &rev[v] { out[pre] -= 1; if out[pre] == 0 { q.push(pre); } } } q.len() as i32
}
```
