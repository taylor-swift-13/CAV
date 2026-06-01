# LC Island Perimeter Rows

## Problem

Return the perimeter of land cells in a semicolon-separated 0/1 grid.

## Requirements

- Rows contain only `0` and `1`.
- All rows have equal positive length.

## Source

- Source: LeetCode problem `island-perimeter`.
- URL: https://leetcode.com/problems/island-perimeter/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcIslandPerimeterRows {
    public static int lc_island_perimeter_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].length(), ans = 0;
        for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (rs[i].charAt(j) == '1') { ans += 4; if (i > 0 && rs[i - 1].charAt(j) == '1') ans -= 2; if (j > 0 && rs[i].charAt(j - 1) == '1') ans -= 2; }
        return ans;
    }
}
```
