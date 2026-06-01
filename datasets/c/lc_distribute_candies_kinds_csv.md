# LC Distribute Candies Kinds CSV

## Problem

Return the maximum number of candy kinds the sister can receive.

## Requirements

- `types` is a comma-separated list of integer candy types.
- The sister receives exactly half of the candies.

## Source

- Source: LeetCode problem `distribute-candies`.
- URL: https://leetcode.com/problems/distribute-candies/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_distribute_candies_kinds_csv(const char *types) {
    int a[512], n = 0, i = 0;
    while (types[i] != '\0') { int sign = 1, v = 0; if (types[i] == '-') { sign = -1; i++; } while (types[i] >= '0' && types[i] <= '9') { v = v * 10 + types[i] - '0'; i++; } a[n++] = sign * v; if (types[i] == ',') i++; }
    int distinct = 0; for (int x = 0; x < n; x++) { int seen = 0; for (int y = 0; y < x; y++) if (a[y] == a[x]) seen = 1; if (!seen) distinct++; } return distinct < n / 2 ? distinct : n / 2;
}
```
