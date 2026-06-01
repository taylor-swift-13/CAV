# LC Minimum Arrows Burst Balloons Count

## Problem

Return the minimum number of arrows needed to burst all balloons.

## Requirements

- Balloons are encoded as `start,end;...`.
- An arrow at coordinate `x` bursts every interval containing `x`.

## Source

- Source: LeetCode problem `minimum-number-of-arrows-to-burst-balloons`.
- URL: https://leetcode.com/problems/minimum-number-of-arrows-to-burst-balloons/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_arrows_burst_balloons_count(points: &str) -> i32 {
    let mut a: Vec<[i32; 2]> = points.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1]] }).collect(); a.sort_by_key(|x| x[1]); let mut arrows = 0; let mut end = i32::MIN; for inr in &a { if arrows == 0 || inr[0] > end { arrows += 1; end = inr[1]; } } arrows
}
```
