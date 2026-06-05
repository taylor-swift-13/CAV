# LC Largest Rectangle Area CSV

## Problem

Return the largest rectangle area in a histogram.

## Requirements

- `heights` is a nonempty comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `largest-rectangle-in-histogram`.
- URL: https://leetcode.com/problems/largest-rectangle-in-histogram/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLargestRectangleAreaCsv {
    public static int lc_largest_rectangle_area_csv(String heights) {
        String[] p = heights.split(","); int n = p.length; int[] h = new int[n + 1]; for (int i = 0; i < n; i++) h[i] = Integer.parseInt(p[i]); int[] st = new int[n + 1]; int top = 0, best = 0; for (int i = 0; i <= n; i++) { while (top > 0 && h[st[top - 1]] > h[i]) { int height = h[st[--top]]; int left = top == 0 ? -1 : st[top - 1]; best = Math.max(best, height * (i - left - 1)); } st[top++] = i; } return best;
    }
}
```
