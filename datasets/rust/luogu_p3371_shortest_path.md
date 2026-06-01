# Luogu P3371 Shortest Path

## Problem

Return the shortest-path distance from source `s` to `target`, or `-1` if unreachable.

## Requirements

- Directed weighted edges are encoded as `u,v,w;...`.
- Vertices are numbered from `1` to `n`.

## Source

- Source: Luogu problem `P3371`.
- URL: https://www.luogu.com.cn/problem/P3371
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p3371_shortest_path(n: i32, edges: &str, s: i32, target: i32) -> i32 {
    let e: Vec<[i32; 3]> = edges.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1], p[2]] }).collect(); let nn = n as usize; let mut dist = vec![1000000000; nn + 1]; let mut used = vec![false; nn + 1]; dist[s as usize] = 0; let mut step = 0usize; while step < nn { let mut node = 0usize; let mut i = 1usize; while i <= nn { if !used[i] && (node == 0 || dist[i] < dist[node]) { node = i; } i += 1; } if node == 0 || dist[node] == 1000000000 { break; } used[node] = true; for edge in &e { if edge[0] as usize == node && dist[node] + edge[2] < dist[edge[1] as usize] { dist[edge[1] as usize] = dist[node] + edge[2]; } } step += 1; } if dist[target as usize] == 1000000000 { -1 } else { dist[target as usize] }
}
```
