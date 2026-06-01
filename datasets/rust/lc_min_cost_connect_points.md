# LC Min Cost Connect Points

## Problem

Return the minimum total Manhattan distance needed to connect all points.

## Requirements

- Points are encoded as `x,y;...`.
- This is the MST objective from the original problem.

## Source

- Source: LeetCode problem `min-cost-to-connect-all-points`.
- URL: https://leetcode.com/problems/min-cost-to-connect-all-points/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_cost_connect_points(points: &str) -> i32 {
    let pts: Vec<(i32,i32)> = points.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); (p[0], p[1]) }).collect(); let n = pts.len(); let mut used = vec![false; n]; let mut dist = vec![1000000000; n]; dist[0] = 0; let mut total = 0; let mut step = 0usize; while step < n { let mut v = n; let mut i = 0usize; while i < n { if !used[i] && (v == n || dist[i] < dist[v]) { v = i; } i += 1; } used[v] = true; total += dist[v]; let mut to = 0usize; while to < n { let w = (pts[v].0 - pts[to].0).abs() + (pts[v].1 - pts[to].1).abs(); if !used[to] && w < dist[to] { dist[to] = w; } to += 1; } step += 1; } total
}
```
