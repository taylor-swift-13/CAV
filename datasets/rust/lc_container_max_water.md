# LC Container Max Water

## Problem

Given `n` vertical line heights, return the maximum water area formed by two different lines.

## Requirements

- `n >= 2` and `height` has at least `n` elements.
- Use only the first `n` heights.
- The result fits in a signed 32-bit integer.

## Source

- Source: LeetCode problem `container-with-most-water`.
- URL: https://leetcode.com/problems/container-with-most-water/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_container_max_water(n: i32, height: &[i32]) -> i32 {
    let mut left = 0usize;
    let mut right = (n - 1) as usize;
    let mut best = 0;
    while left < right {
        let h = if height[left] < height[right] { height[left] } else { height[right] };
        let area = h * (right - left) as i32;
        if area > best { best = area; }
        if height[left] < height[right] { left += 1; }
        else { right -= 1; }
    }
    best
}
```
