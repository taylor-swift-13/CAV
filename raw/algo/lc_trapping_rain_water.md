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

```c
int lc_trapping_rain_water(int n, int *height) {
    int left = 0, right = n - 1;
    int left_max = 0, right_max = 0;
    int water = 0;
    while (left <= right) {
        if (left_max <= right_max) {
            if (height[left] < left_max) water += left_max - height[left];
            else left_max = height[left];
            left++;
        } else {
            if (height[right] < right_max) water += right_max - height[right];
            else right_max = height[right];
            right--;
        }
    }
    return water;
}
```
