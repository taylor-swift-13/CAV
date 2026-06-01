# LC Merge Intervals Total Length

## Problem

Merge overlapping intervals and return the total covered length.

## Requirements

- Intervals are encoded as `start,end;...`.
- Touching intervals merge as in the original problem.

## Source

- Source: LeetCode problem `merge-intervals`.
- URL: https://leetcode.com/problems/merge-intervals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMergeIntervalsTotalLength {
    public static int lc_merge_intervals_total_length(String intervals) {
        String[] rows = intervals.split(";"); int[][] a = new int[rows.length][2]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(","); a[i][0] = Integer.parseInt(p[0]); a[i][1] = Integer.parseInt(p[1]); } java.util.Arrays.sort(a, (x, y) -> Integer.compare(x[0], y[0])); int total = 0, s = a[0][0], e = a[0][1]; for (int i = 1; i < a.length; i++) { if (a[i][0] <= e) e = Math.max(e, a[i][1]); else { total += e - s; s = a[i][0]; e = a[i][1]; } } return total + e - s;
    }
}
```
