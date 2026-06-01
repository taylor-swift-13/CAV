# LC Gas Station Start CSV

## Problem

Return the starting gas station index that completes the circuit, or `-1`.

## Requirements

- `gas` and `cost` are comma-separated arrays of equal positive length.
- The original problem guarantees uniqueness when a solution exists.

## Source

- Source: LeetCode problem `gas-station`.
- URL: https://leetcode.com/problems/gas-station/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_gas_station_start_csv(gas: &str, cost: &str) -> i32 {
    let g: Vec<i32> = gas.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let c: Vec<i32> = cost.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut total = 0; let mut tank = 0; let mut start = 0; let mut i = 0usize; while i < g.len() { let d = g[i] - c[i]; total += d; tank += d; if tank < 0 { start = i as i32 + 1; tank = 0; } i += 1; } if total >= 0 { start } else { -1 }
}
```
