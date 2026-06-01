# LC Subarray Product Less Than K CSV

## Problem

Return how many contiguous subarrays have product strictly less than `k`.

## Requirements

- `nums` is a nonempty comma-separated list of positive integers.
- `k >= 0`.

## Source

- Source: LeetCode problem `subarray-product-less-than-k`.
- URL: https://leetcode.com/problems/subarray-product-less-than-k/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_subarray_product_less_than_k_csv(nums: &str, k: i32) -> i32 {
    if k <= 1 { return 0; } let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut left = 0usize; let mut prod = 1; let mut ans = 0; let mut right = 0usize; while right < a.len() { prod *= a[right]; while prod >= k { prod /= a[left]; left += 1; } ans += (right - left + 1) as i32; right += 1; } ans
}
```
