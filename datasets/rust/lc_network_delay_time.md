# LC Network Delay Time

## Problem

Return the time for all nodes to receive a signal, or `-1`.

## Requirements

- Directed weighted edges are encoded as `u,v,w;...`.
- Nodes are numbered from `1` to `n`.

## Source

- Source: LeetCode problem `network-delay-time`.
- URL: https://leetcode.com/problems/network-delay-time/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_network_delay_time(times: &str, n: i32, k: i32) -> i32 {
    let edges: Vec<[i32; 3]> = times.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1], p[2]] }).collect(); let nn = n as usize; let mut dist = vec![1000000000; nn + 1]; let mut used = vec![false; nn + 1]; dist[k as usize] = 0; let mut step = 0usize; while step < nn { let mut node = 0usize; let mut i = 1usize; while i <= nn { if !used[i] && (node == 0 || dist[i] < dist[node]) { node = i; } i += 1; } if node == 0 || dist[node] == 1000000000 { break; } used[node] = true; for e in &edges { if e[0] as usize == node && dist[node] + e[2] < dist[e[1] as usize] { dist[e[1] as usize] = dist[node] + e[2]; } } step += 1; } let mut ans = 0; let mut i = 1usize; while i <= nn { if dist[i] == 1000000000 { return -1; } if dist[i] > ans { ans = dist[i]; } i += 1; } ans
}
```
