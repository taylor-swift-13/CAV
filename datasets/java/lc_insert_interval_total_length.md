# LC Insert Interval Total Length

## Problem

Insert a new interval, merge overlaps, and return the total covered length.

## Requirements

- Existing intervals are encoded as `start,end;...`.
- Existing intervals are sorted and non-overlapping.

## Source

- Source: LeetCode problem `insert-interval`.
- URL: https://leetcode.com/problems/insert-interval/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcInsertIntervalTotalLength {
    public static int lc_insert_interval_total_length(String intervals, int new_start, int new_end) {
        String[] rows = intervals.split(";"); int[][] a = new int[rows.length + 1][2]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(","); a[i][0] = Integer.parseInt(p[0]); a[i][1] = Integer.parseInt(p[1]); } a[rows.length][0] = new_start; a[rows.length][1] = new_end; java.util.Arrays.sort(a, (x, y) -> Integer.compare(x[0], y[0])); int total = 0, s = a[0][0], e = a[0][1]; for (int i = 1; i < a.length; i++) { if (a[i][0] <= e) e = Math.max(e, a[i][1]); else { total += e - s; s = a[i][0]; e = a[i][1]; } } return total + e - s;
    }
}
```
