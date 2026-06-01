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

```java
class LcContainerMaxWater {
    public static int lc_container_max_water(int n, int[] height) {
        int left = 0;
        int right = n - 1;
        int best = 0;
        while (left < right) {
            int h = height[left] < height[right] ? height[left] : height[right];
            int area = h * (right - left);
            if (area > best) best = area;
            if (height[left] < height[right]) left++;
            else right--;
        }
        return best;
    }
}
```
