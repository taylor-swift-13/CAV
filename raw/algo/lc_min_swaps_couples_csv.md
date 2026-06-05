# LC Couples Holding Hands Min Swaps CSV

## Problem

Return the minimum adjacent-seat swaps needed so every couple sits together.

## Requirements

- `row` is a comma-separated seating arrangement.
- Couples are `(0,1)`, `(2,3)`, and so on.

## Source

- Source: LeetCode problem `couples-holding-hands`.
- URL: https://leetcode.com/problems/couples-holding-hands/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_min_swaps_couples_csv(const char *row) {
    int a[512], pos[512], n = 0, i = 0; while (row[i] != '\0') { int v = 0; while (row[i] >= '0' && row[i] <= '9') { v = v * 10 + (row[i] - '0'); i++; } a[n] = v; pos[v] = n; n++; if (row[i] == ',') i++; } int swaps = 0; for (int seat = 0; seat < n; seat += 2) { int x = a[seat], mate = x ^ 1; if (a[seat + 1] != mate) { int mpos = pos[mate], other = a[seat + 1]; a[mpos] = other; pos[other] = mpos; a[seat + 1] = mate; pos[mate] = seat + 1; swaps++; } } return swaps;
}
```
