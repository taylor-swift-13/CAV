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

```java
class LcTrappingRainWater {
    public static int lc_trapping_rain_water(int n, int[] height) {
        int left = 0, right = n - 1;
        int leftMax = 0, rightMax = 0;
        int water = 0;
        while (left <= right) {
            if (leftMax <= rightMax) {
                if (height[left] < leftMax) water += leftMax - height[left];
                else leftMax = height[left];
                left++;
            } else {
                if (height[right] < rightMax) water += rightMax - height[right];
                else rightMax = height[right];
                right--;
            }
        }
        return water;
    }
}
```
