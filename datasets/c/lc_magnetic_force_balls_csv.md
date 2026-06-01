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

```c
int lc_magnetic_force_balls_csv(const char *position, int m) {
    int a[512], n = 0, i = 0; while (position[i] != '\0') { int v = 0; while (position[i] >= '0' && position[i] <= '9') { v = v * 10 + position[i] - '0'; i++; } a[n++] = v; if (position[i] == ',') i++; } for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; } int lo = 1, hi = a[n - 1] - a[0], ans = 1; while (lo <= hi) { int mid = lo + (hi - lo) / 2, count = 1, last = a[0]; for (int x = 1; x < n; x++) if (a[x] - last >= mid) { count++; last = a[x]; } if (count >= m) { ans = mid; lo = mid + 1; } else hi = mid - 1; } return ans;
}
```
