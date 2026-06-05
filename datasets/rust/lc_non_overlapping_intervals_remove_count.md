# LC Non Overlapping Intervals Remove Count

## Problem

Return the minimum number of intervals to remove so the rest do not overlap.

## Requirements

- Intervals are encoded as `start,end;...`.
- Use half-open overlap semantics matching the original problem examples.

## Source

- Source: LeetCode problem `non-overlapping-intervals`.
- URL: https://leetcode.com/problems/non-overlapping-intervals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_non_overlapping_intervals_remove_count(intervals: &str) -> i32 {
    let mut a: Vec<[i32; 2]> = intervals.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1]] }).collect(); a.sort_by_key(|x| x[1]); let mut keep = 0; let mut end = i32::MIN; for inr in &a { if inr[0] >= end { keep += 1; end = inr[1]; } } a.len() as i32 - keep
}
```
