# Luogu P3366 MST Weight

## Problem

Return the total weight of a minimum spanning tree, or `-1` if the graph is disconnected.

## Requirements

- Undirected weighted edges are encoded as `u,v,w;...`.
- Vertices are numbered from `1` to `n`.

## Source

- Source: Luogu problem `P3366`.
- URL: https://www.luogu.com.cn/problem/P3366
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p3366_mst_weight(n: i32, edges: &str) -> i32 {
    let mut e: Vec<[i32; 3]> = edges.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1], p[2]] }).collect(); e.sort_by_key(|x| x[2]); let mut parent: Vec<usize> = (0..=n as usize).collect(); fn find(parent: &mut Vec<usize>, x: usize) -> usize { if parent[x] != x { let r = find(parent, parent[x]); parent[x] = r; } parent[x] } let mut total = 0; let mut used = 0; for edge in e { let a = find(&mut parent, edge[0] as usize); let b = find(&mut parent, edge[1] as usize); if a != b { parent[a] = b; total += edge[2]; used += 1; } } if used == n - 1 { total } else { -1 }
}
```
