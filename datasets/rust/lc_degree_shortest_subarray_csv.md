# LC Degree Of Array Shortest Subarray CSV

## Problem

Return the shortest contiguous subarray length with the same degree as the whole array.

## Requirements

- `nums` is a nonempty comma-separated list of nonnegative integers less than 1000.

## Source

- Source: LeetCode problem `degree-of-an-array`.
- URL: https://leetcode.com/problems/degree-of-an-array/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_degree_shortest_subarray_csv(nums: &str) -> i32 {
    let a: Vec<usize> = nums.split(',').map(|x| x.parse::<usize>().unwrap()).collect(); let mut first = vec![-1i32; 1000]; let mut count = vec![0i32; 1000]; let mut degree = 0; let mut best = 1000000; for (i, &v) in a.iter().enumerate() { if first[v] < 0 { first[v] = i as i32; } count[v] += 1; let len = i as i32 - first[v] + 1; if count[v] > degree { degree = count[v]; best = len; } else if count[v] == degree && len < best { best = len; } } best
}
```
