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

```c
int lc_car_fleet_count(int target, const char *position, const char *speed) {
    int p[256], s[256], n = 0, i = 0; while (position[i] != '\0') { int v = 0; while (position[i] >= '0' && position[i] <= '9') { v = v * 10 + (position[i] - '0'); i++; } p[n++] = v; if (position[i] == ',') i++; } i = 0; int m = 0; while (speed[i] != '\0') { int v = 0; while (speed[i] >= '0' && speed[i] <= '9') { v = v * 10 + (speed[i] - '0'); i++; } s[m++] = v; if (speed[i] == ',') i++; }
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (p[y] > p[x]) { int tp = p[x], ts = s[x]; p[x] = p[y]; s[x] = s[y]; p[y] = tp; s[y] = ts; }
    int fleets = 0; double slow = -1.0; for (int x = 0; x < n; x++) { double t = (double)(target - p[x]) / (double)s[x]; if (t > slow) { fleets++; slow = t; } } return fleets;
}
```
