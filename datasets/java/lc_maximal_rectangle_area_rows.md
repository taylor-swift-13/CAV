# LC Maximal Rectangle Area Rows

## Problem

Return the area of the largest all-1 rectangle in a semicolon-separated binary matrix.

## Requirements

- Rows contain only `0` and `1`.
- All rows have equal positive length.
- The empty string returns `0`.

## Source

- Source: LeetCode problem `maximal-rectangle`.
- URL: https://leetcode.com/problems/maximal-rectangle/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMaximalRectangleAreaRows {
    public static int lc_maximal_rectangle_area_rows(String rows) {
        if (rows.isEmpty()) return 0; String[] rs = rows.split(";"); int r = rs.length, c = rs[0].length(), best = 0; int[] h = new int[c], st = new int[c + 1];
        for (int i = 0; i < r; i++) { for (int j = 0; j < c; j++) h[j] = rs[i].charAt(j) == '1' ? h[j] + 1 : 0; int top = 0; for (int j = 0; j <= c; j++) { int cur = j == c ? 0 : h[j]; while (top > 0 && h[st[top - 1]] > cur) { int height = h[st[--top]]; int left = top == 0 ? -1 : st[top - 1]; int area = height * (j - left - 1); if (area > best) best = area; } st[top++] = j; } } return best;
    }
}
```
