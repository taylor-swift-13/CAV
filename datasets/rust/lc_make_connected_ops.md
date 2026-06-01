# LC Network Connected Operations

## Problem

Return the minimum cable moves needed to connect all computers, or `-1` if impossible.

## Requirements

- Connections are encoded as `u,v;...`.
- Computers are numbered from `0` to `n-1`.

## Source

- Source: LeetCode problem `number-of-operations-to-make-network-connected`.
- URL: https://leetcode.com/problems/number-of-operations-to-make-network-connected/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_make_connected_ops(n: i32, connections: &str) -> i32 {
    let nn = n as usize; let mut g = vec![vec![false; nn]; nn]; let mut edges = 0; if !connections.is_empty() { for e in connections.split(';') { let p: Vec<usize> = e.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); g[p[0]][p[1]] = true; g[p[1]][p[0]] = true; edges += 1; } } if edges < n - 1 { return -1; } let mut seen = vec![false; nn]; let mut comps = 0; let mut s = 0usize; while s < nn { if !seen[s] { comps += 1; let mut q = vec![s]; let mut head = 0usize; seen[s] = true; while head < q.len() { let v = q[head]; head += 1; let mut to = 0usize; while to < nn { if g[v][to] && !seen[to] { seen[to] = true; q.push(to); } to += 1; } } } s += 1; } comps - 1
}
```
