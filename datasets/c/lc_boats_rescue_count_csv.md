# LC Boats To Save People Count CSV

## Problem

Return the minimum number of boats needed to rescue everyone.

## Requirements

- `people` is a comma-separated list of weights.
- Each boat carries at most two people with total weight at most `limit`.

## Source

- Source: LeetCode problem `boats-to-save-people`.
- URL: https://leetcode.com/problems/boats-to-save-people/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_boats_rescue_count_csv(const char *people, int limit) {
    int a[512], n = 0, i = 0; while (people[i] != '\0') { int v = 0; while (people[i] >= '0' && people[i] <= '9') { v = v * 10 + people[i] - '0'; i++; } a[n++] = v; if (people[i] == ',') i++; } for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; } int l = 0, r = n - 1, boats = 0; while (l <= r) { if (a[l] + a[r] <= limit) l++; r--; boats++; } return boats;
}
```
