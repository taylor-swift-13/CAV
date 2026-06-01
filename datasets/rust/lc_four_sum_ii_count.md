# LC 4Sum II Count

## Problem

Return the number of tuples `i,j,k,l` with `a[i]+b[j]+c[k]+d[l] == 0`.

## Requirements

- Arrays are comma-separated signed integer lists.

## Source

- Source: LeetCode problem `4sum-ii`.
- URL: https://leetcode.com/problems/4sum-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_four_sum_ii_count(a: &str, b: &str, c: &str, d: &str) -> i32 {
    let aa: Vec<i32> = a.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let bb: Vec<i32> = b.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let cc: Vec<i32> = c.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let dd: Vec<i32> = d.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut ans = 0; for &x in &aa { for &y in &bb { for &z in &cc { for &w in &dd { if x + y + z + w == 0 { ans += 1; } } } } } ans
}
```
