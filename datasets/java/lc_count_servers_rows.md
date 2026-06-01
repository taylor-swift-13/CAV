# LC Count Servers That Communicate Rows

## Problem

Return how many servers can communicate with at least one other server in the same row or column.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.

## Source

- Source: LeetCode problem `count-servers-that-communicate`.
- URL: https://leetcode.com/problems/count-servers-that-communicate/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcCountServersRows {
    public static int lc_count_servers_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].length(); int[] row = new int[r], col = new int[c]; for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (rs[i].charAt(j) == '1') { row[i]++; col[j]++; } int ans = 0; for (int i = 0; i < r; i++) for (int j = 0; j < c; j++) if (rs[i].charAt(j) == '1' && (row[i] > 1 || col[j] > 1)) ans++; return ans;
    }
}
```
