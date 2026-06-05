# LC Merge Intervals Total Length

## Problem

Merge overlapping intervals and return the total covered length.

## Requirements

- Intervals are encoded as `start,end;...`.
- Touching intervals merge as in the original problem.

## Source

- Source: LeetCode problem `merge-intervals`.
- URL: https://leetcode.com/problems/merge-intervals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_merge_intervals_total_length(intervals: &str) -> i32 {
    let mut a: Vec<[i32; 2]> = intervals.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1]] }).collect(); a.sort_by_key(|x| x[0]); let mut total = 0; let mut s = a[0][0]; let mut e = a[0][1]; for inr in a.iter().skip(1) { if inr[0] <= e { if inr[1] > e { e = inr[1]; } } else { total += e - s; s = inr[0]; e = inr[1]; } } total + e - s
}
```
