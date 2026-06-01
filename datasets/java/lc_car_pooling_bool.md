# LC Car Pooling Bool

## Problem

Return true if all trips can be served without exceeding capacity.

## Requirements

- Trips are encoded as `passengers,from,to;...`.
- Locations are nonnegative integers.

## Source

- Source: LeetCode problem `car-pooling`.
- URL: https://leetcode.com/problems/car-pooling/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcCarPoolingBool {
    public static boolean lc_car_pooling_bool(String trips, int capacity) {
        int[] diff = new int[1001]; for (String row : trips.split(";")) { String[] p = row.split(","); int pass = Integer.parseInt(p[0]), from = Integer.parseInt(p[1]), to = Integer.parseInt(p[2]); diff[from] += pass; diff[to] -= pass; } int load = 0; for (int x : diff) { load += x; if (load > capacity) return false; } return true;
    }
}
```
