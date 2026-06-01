# LC Swim In Rising Water Time Rows

## Problem

Return the minimum time needed to reach the bottom-right cell.

## Requirements

- Grid values are encoded as semicolon-separated comma rows.
- You may move 4-directionally through cells whose value is at most the current time.

## Source

- Source: LeetCode problem `swim-in-rising-water`.
- URL: https://leetcode.com/problems/swim-in-rising-water/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_swim_rising_water_time_rows(rows: &str) -> i32 {
    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let r = a.len(); let c = a[0].len(); let total = r * c; let mut dist = vec![1000000000; total]; let mut used = vec![false; total]; dist[0] = a[0][0]; let dirs = [(1i32,0i32),(-1,0),(0,1),(0,-1)]; let mut step = 0usize; while step < total { let mut node = total; let mut i = 0usize; while i < total { if !used[i] && (node == total || dist[i] < dist[node]) { node = i; } i += 1; } if node == total - 1 { break; } used[node] = true; let x = node / c; let y = node % c; for &(dx,dy) in dirs.iter() { let nx = x as i32 + dx; let ny = y as i32 + dy; if nx >= 0 && nx < r as i32 && ny >= 0 && ny < c as i32 { let ni = nx as usize * c + ny as usize; let nd = dist[node].max(a[nx as usize][ny as usize]); if nd < dist[ni] { dist[ni] = nd; } } } step += 1; } dist[total - 1]
}
```
