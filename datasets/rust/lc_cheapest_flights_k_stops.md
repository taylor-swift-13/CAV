# LC Cheapest Flights Within K Stops

## Problem

Return the cheapest price from `src` to `dst` using at most `k` stops, or `-1`.

## Requirements

- Flights are encoded as `from,to,price;...`.
- Cities are numbered from `0` to `n-1`.

## Source

- Source: LeetCode problem `cheapest-flights-within-k-stops`.
- URL: https://leetcode.com/problems/cheapest-flights-within-k-stops/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_cheapest_flights_k_stops(n: i32, flights: &str, src: i32, dst: i32, k: i32) -> i32 {
    let edges: Vec<[usize; 3]> = flights.split(';').map(|r| { let p: Vec<usize> = r.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); [p[0], p[1], p[2]] }).collect(); let nn = n as usize; let inf = 1000000000; let mut dist = vec![inf; nn]; dist[src as usize] = 0; let mut step = 0; while step <= k { let mut next = dist.clone(); for e in &edges { if dist[e[0]] != inf && dist[e[0]] + (e[2] as i32) < next[e[1]] { next[e[1]] = dist[e[0]] + (e[2] as i32); } } dist = next; step += 1; } if dist[dst as usize] == inf { -1 } else { dist[dst as usize] }
}
```
