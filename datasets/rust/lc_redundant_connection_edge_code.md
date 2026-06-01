# LC Redundant Connection Edge Code

## Problem

Return the redundant undirected edge encoded as `u * 1000 + v`.

## Requirements

- `edges` is semicolon-separated `u,v` pairs.
- Return the last edge whose addition creates a cycle.

## Source

- Source: LeetCode problem `redundant-connection`.
- URL: https://leetcode.com/problems/redundant-connection/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_redundant_connection_edge_code(edges: &str) -> i32 {
    fn find(parent: &mut Vec<usize>, mut x: usize) -> usize { while parent[x] != x { let px = parent[x]; parent[x] = parent[px]; x = parent[x]; } x }
    let mut parent: Vec<usize> = (0..=1000).collect(); let mut ans = 0; for e in edges.split(';') { let p: Vec<usize> = e.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); let ru = find(&mut parent, p[0]); let rv = find(&mut parent, p[1]); if ru == rv { ans = (p[0] * 1000 + p[1]) as i32; } else { parent[ru] = rv; } } ans
}
```
