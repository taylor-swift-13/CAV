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

```c
int lc_car_pooling_bool(const char *trips, int capacity) {
    int diff[1001] = {0}, i = 0; while (trips[i] != '\0') { int v[3]; for (int k = 0; k < 3; k++) { int x = 0; while (trips[i] >= '0' && trips[i] <= '9') { x = x * 10 + trips[i] - '0'; i++; } v[k] = x; if (trips[i] == ',') i++; } diff[v[1]] += v[0]; diff[v[2]] -= v[0]; if (trips[i] == ';') i++; } int load = 0; for (int x = 0; x <= 1000; x++) { load += diff[x]; if (load > capacity) return 0; } return 1;
}
```
