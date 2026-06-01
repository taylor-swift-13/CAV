# LC Number Of Provinces Rows

## Problem

Return the number of connected components in an adjacency matrix.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.
- The matrix is square.

## Source

- Source: LeetCode problem `number-of-provinces`.
- URL: https://leetcode.com/problems/number-of-provinces/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcNumberOfProvincesRows {
    public static int lc_number_of_provinces_rows(String rows) {
        String[] rs = rows.split(";"); int n = rs.length, ans = 0; boolean[] seen = new boolean[n]; int[] stack = new int[n]; for (int s = 0; s < n; s++) if (!seen[s]) { ans++; int top = 0; stack[top++] = s; seen[s] = true; while (top > 0) { int v = stack[--top]; for (int to = 0; to < n; to++) if (rs[v].charAt(to) == '1' && !seen[to]) { seen[to] = true; stack[top++] = to; } } } return ans;
    }
}
```
