# LC Number Of LIS Count CSV

## Problem

Return how many longest increasing subsequences exist.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.

## Source

- Source: LeetCode problem `number-of-longest-increasing-subsequence`.
- URL: https://leetcode.com/problems/number-of-longest-increasing-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_number_of_lis_count_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let n = a.len(); let mut len = vec![1; n]; let mut cnt = vec![1; n]; let mut best = 0; let mut ans = 0; let mut i = 0usize; while i < n { let mut j = 0usize; while j < i { if a[j] < a[i] { if len[j] + 1 > len[i] { len[i] = len[j] + 1; cnt[i] = cnt[j]; } else if len[j] + 1 == len[i] { cnt[i] += cnt[j]; } } j += 1; } if len[i] > best { best = len[i]; ans = cnt[i]; } else if len[i] == best { ans += cnt[i]; } i += 1; } ans
}
```
