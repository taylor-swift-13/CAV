# LC Insert Interval Total Length

## Problem

Insert a new interval, merge overlaps, and return the total covered length.

## Requirements

- Existing intervals are encoded as `start,end;...`.
- Existing intervals are sorted and non-overlapping.

## Source

- Source: LeetCode problem `insert-interval`.
- URL: https://leetcode.com/problems/insert-interval/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_insert_interval_total_length(intervals: &str, new_start: i32, new_end: i32) -> i32 {
    let mut a: Vec<[i32; 2]> = intervals.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1]] }).collect(); a.push([new_start, new_end]); a.sort_by_key(|x| x[0]); let mut total = 0; let mut s = a[0][0]; let mut e = a[0][1]; for inr in a.iter().skip(1) { if inr[0] <= e { if inr[1] > e { e = inr[1]; } } else { total += e - s; s = inr[0]; e = inr[1]; } } total + e - s
}
```
