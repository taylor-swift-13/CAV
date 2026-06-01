# LC Trapping Rain Water

## Problem

Given `n` bar heights, return how many units of rain water are trapped after raining.

## Requirements

- `n >= 0` and `height` has at least `n` elements.
- All heights are nonnegative.
- Use only the first `n` elements.

## Source

- Source: LeetCode problem `trapping-rain-water`.
- URL: https://leetcode.com/problems/trapping-rain-water/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_trapping_rain_water(n: i32, height: &[i32]) -> i32 {
    let mut left = 0i32;
    let mut right = n - 1;
    let mut left_max = 0;
    let mut right_max = 0;
    let mut water = 0;
    while left <= right {
        if left_max <= right_max {
            let h = height[left as usize];
            if h < left_max { water += left_max - h; }
            else { left_max = h; }
            left += 1;
        } else {
            let h = height[right as usize];
            if h < right_max { water += right_max - h; }
            else { right_max = h; }
            right -= 1;
        }
    }
    water
}
```
