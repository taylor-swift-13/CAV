# LC Possible Bipartition Bool

## Problem

Return true if people can be split into two groups so no dislike pair is inside a group.

## Requirements

- Dislike pairs are encoded as `a,b;...`.
- People are numbered from `1` to `n`.

## Source

- Source: LeetCode problem `possible-bipartition`.
- URL: https://leetcode.com/problems/possible-bipartition/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_possible_bipartition_bool(n: i32, dislikes: &str) -> bool {
    let nn = n as usize; let mut g = vec![vec![false; nn + 1]; nn + 1]; for row in dislikes.split(';') { let p: Vec<usize> = row.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); g[p[0]][p[1]] = true; g[p[1]][p[0]] = true; } let mut color = vec![-1; nn + 1]; let mut s = 1usize; while s <= nn { if color[s] < 0 { let mut q = vec![s]; let mut head = 0usize; color[s] = 0; while head < q.len() { let v = q[head]; head += 1; let mut to = 1usize; while to <= nn { if g[v][to] { if color[to] < 0 { color[to] = 1 - color[v]; q.push(to); } else if color[to] == color[v] { return false; } } to += 1; } } } s += 1; } true
}
```
