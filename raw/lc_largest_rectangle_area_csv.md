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

```c
int lc_largest_rectangle_area_csv(const char *heights) {
    int h[512], n = 0, i = 0; while (heights[i] != '\0') { int v = 0; while (heights[i] >= '0' && heights[i] <= '9') { v = v * 10 + (heights[i] - '0'); i++; } h[n++] = v; if (heights[i] == ',') i++; } h[n] = 0;
    int st[513], top = 0, best = 0; for (int idx = 0; idx <= n; idx++) { while (top > 0 && h[st[top - 1]] > h[idx]) { int height = h[st[--top]]; int left = top == 0 ? -1 : st[top - 1]; int area = height * (idx - left - 1); if (area > best) best = area; } st[top++] = idx; } return best;
}
```
