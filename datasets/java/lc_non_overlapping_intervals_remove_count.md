# LC Non Overlapping Intervals Remove Count

## Problem

Return the minimum number of intervals to remove so the rest do not overlap.

## Requirements

- Intervals are encoded as `start,end;...`.
- Use half-open overlap semantics matching the original problem examples.

## Source

- Source: LeetCode problem `non-overlapping-intervals`.
- URL: https://leetcode.com/problems/non-overlapping-intervals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcNonOverlappingIntervalsRemoveCount {
    public static int lc_non_overlapping_intervals_remove_count(String intervals) {
        String[] rows = intervals.split(";"); int[][] a = new int[rows.length][2]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(","); a[i][0] = Integer.parseInt(p[0]); a[i][1] = Integer.parseInt(p[1]); } java.util.Arrays.sort(a, (x, y) -> x[1] - y[1]); int keep = 0, end = Integer.MIN_VALUE; for (int[] in : a) if (in[0] >= end) { keep++; end = in[1]; } return a.length - keep;
    }
}
```
