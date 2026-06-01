# LC Minimum Arrows Burst Balloons Count

## Problem

Return the minimum number of arrows needed to burst all balloons.

## Requirements

- Balloons are encoded as `start,end;...`.
- An arrow at coordinate `x` bursts every interval containing `x`.

## Source

- Source: LeetCode problem `minimum-number-of-arrows-to-burst-balloons`.
- URL: https://leetcode.com/problems/minimum-number-of-arrows-to-burst-balloons/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcArrowsBurstBalloonsCount {
    public static int lc_arrows_burst_balloons_count(String points) {
        String[] rows = points.split(";"); int[][] a = new int[rows.length][2]; for (int i = 0; i < rows.length; i++) { String[] p = rows[i].split(","); a[i][0] = Integer.parseInt(p[0]); a[i][1] = Integer.parseInt(p[1]); } java.util.Arrays.sort(a, (x, y) -> Integer.compare(x[1], y[1])); int arrows = 0, end = Integer.MIN_VALUE; for (int[] in : a) if (arrows == 0 || in[0] > end) { arrows++; end = in[1]; } return arrows;
    }
}
```
