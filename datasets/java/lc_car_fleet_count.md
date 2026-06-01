# LC Car Fleet Count

## Problem

Return how many car fleets arrive at the target.

## Requirements

- `position` and `speed` are comma-separated lists of equal length.
- Positions are distinct and less than target.

## Source

- Source: LeetCode problem `car-fleet`.
- URL: https://leetcode.com/problems/car-fleet/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcCarFleetCount {
    public static int lc_car_fleet_count(int target, String position, String speed) {
        String[] pp = position.split(","), ss = speed.split(","); int n = pp.length; int[][] cars = new int[n][2]; for (int i = 0; i < n; i++) { cars[i][0] = Integer.parseInt(pp[i]); cars[i][1] = Integer.parseInt(ss[i]); } java.util.Arrays.sort(cars, (a, b) -> b[0] - a[0]); int fleets = 0; double slow = -1.0; for (int[] car : cars) { double t = (double)(target - car[0]) / car[1]; if (t > slow) { fleets++; slow = t; } } return fleets;
    }
}
```
