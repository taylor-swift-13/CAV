# LC Magnetic Force Between Balls CSV

## Problem

Return the largest minimum distance between any two placed balls.

## Requirements

- `position` is a comma-separated list of basket positions.
- Place exactly `m` balls.

## Source

- Source: LeetCode problem `magnetic-force-between-two-balls`.
- URL: https://leetcode.com/problems/magnetic-force-between-two-balls/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMagneticForceBallsCsv {
    public static int lc_magnetic_force_balls_csv(String position, int m) {
        String[] p = position.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a); int lo = 1, hi = a[a.length - 1] - a[0], ans = 1; while (lo <= hi) { int mid = lo + (hi - lo) / 2, count = 1, last = a[0]; for (int i = 1; i < a.length; i++) if (a[i] - last >= mid) { count++; last = a[i]; } if (count >= m) { ans = mid; lo = mid + 1; } else hi = mid - 1; } return ans;
    }
}
```
