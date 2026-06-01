# LC Majority Element II Count CSV

## Problem

Return how many distinct values appear more than `n/3` times.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.
- The answer is at most 2.

## Source

- Source: LeetCode problem `majority-element-ii`.
- URL: https://leetcode.com/problems/majority-element-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_majority_element_ii_count_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut ans = 0; let mut i = 0usize; while i < a.len() { let mut seen = false; let mut j = 0usize; while j < i { if a[j] == a[i] { seen = true; } j += 1; } if !seen { let mut cnt = 0; for &v in &a { if v == a[i] { cnt += 1; } } if cnt > a.len() as i32 / 3 { ans += 1; } } i += 1; } ans
}
```
