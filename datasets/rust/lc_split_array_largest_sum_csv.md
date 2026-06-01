# LC Split Array Largest Sum CSV

## Problem

Split `nums` into `m` nonempty contiguous parts and minimize the largest part sum.

## Requirements

- `nums` is a comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `split-array-largest-sum`.
- URL: https://leetcode.com/problems/split-array-largest-sum/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_split_array_largest_sum_csv(nums: &str, m: i32) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut lo = *a.iter().max().unwrap(); let mut hi: i32 = a.iter().sum(); while lo < hi { let mid = lo + (hi - lo) / 2; let mut parts = 1; let mut sum = 0; for &v in &a { if sum + v > mid { parts += 1; sum = 0; } sum += v; } if parts <= m { hi = mid; } else { lo = mid + 1; } } lo
}
```
