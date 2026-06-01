# Luogu P1803 Interval Schedule Count

## Problem

Return the maximum number of non-overlapping intervals that can be selected.

## Requirements

- Intervals are encoded as `start,end;...`.
- Select by earliest finishing time.

## Source

- Source: Luogu problem `P1803`.
- URL: https://www.luogu.com.cn/problem/P1803
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p1803_interval_schedule_count(intervals: &str) -> i32 {
    let mut a: Vec<[i32; 2]> = intervals.split(';').map(|r| { let p: Vec<i32> = r.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); [p[0], p[1]] }).collect(); a.sort_by_key(|x| x[1]); let mut ans = 0; let mut end = -1; for inr in &a { if inr[0] >= end { ans += 1; end = inr[1]; } } ans
}
```
