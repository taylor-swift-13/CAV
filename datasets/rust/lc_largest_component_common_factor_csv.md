# LC Largest Component By Common Factor CSV

## Problem

Return the size of the largest component where two numbers are connected if they share a factor greater than 1.

## Requirements

- `nums` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `largest-component-size-by-common-factor`.
- URL: https://leetcode.com/problems/largest-component-size-by-common-factor/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_largest_component_common_factor_csv(nums: &str) -> i32 {
    fn gcd(mut a: i32, mut b: i32) -> i32 { while b != 0 { let t = a % b; a = b; b = t; } a } let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let n = a.len(); let mut g = vec![vec![false; n]; n]; let mut i = 0usize; while i < n { let mut j = i + 1; while j < n { if gcd(a[i], a[j]) > 1 { g[i][j] = true; g[j][i] = true; } j += 1; } i += 1; } let mut seen = vec![false; n]; let mut best = 0; let mut s = 0usize; while s < n { if !seen[s] { let mut q = vec![s]; let mut head = 0usize; let mut cnt = 0; seen[s] = true; while head < q.len() { let v = q[head]; head += 1; cnt += 1; let mut to = 0usize; while to < n { if g[v][to] && !seen[to] { seen[to] = true; q.push(to); } to += 1; } } if cnt > best { best = cnt; } } s += 1; } best
}
```
