# LC Daily Temperatures Wait Sum CSV

## Problem

Compute daily-temperature waiting days and return their sum.

## Requirements

- `temps` is a nonempty comma-separated list of integers.
- For days with no warmer future day, the wait is `0`.

## Source

- Source: LeetCode problem `daily-temperatures`.
- URL: https://leetcode.com/problems/daily-temperatures/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_daily_temperatures_wait_sum_csv(temps: &str) -> i32 {
    let a: Vec<i32> = temps.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut st: Vec<usize> = Vec::new(); let mut sum = 0;
    let mut d = 0usize; while d < a.len() { while !st.is_empty() && a[d] > a[*st.last().unwrap()] { let prev = st.pop().unwrap(); sum += (d - prev) as i32; } st.push(d); d += 1; }
    sum
}
```
