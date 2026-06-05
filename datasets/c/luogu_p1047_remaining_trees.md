# Luogu P1047 Remaining Trees

## Problem

Return how many integer tree positions remain after removing all interval-covered positions.

## Requirements

- The road has tree positions from `0` through `length`, inclusive.
- `intervals` is semicolon-separated `left,right` records with inclusive endpoints.

## Source

- Source: Luogu problem `P1047`.
- URL: https://www.luogu.com.cn/problem/P1047
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p1047_remaining_trees(int length, const char *intervals) {
    int removed[10001] = {0}, i = 0; while (intervals[i] != '\0') { int l = 0, r = 0; while (intervals[i] >= '0' && intervals[i] <= '9') { l = l * 10 + intervals[i] - '0'; i++; } if (intervals[i] == ',') i++; while (intervals[i] >= '0' && intervals[i] <= '9') { r = r * 10 + intervals[i] - '0'; i++; } for (int x = l; x <= r && x <= length; x++) removed[x] = 1; if (intervals[i] == ';') i++; } int ans = 0; for (int x = 0; x <= length; x++) if (!removed[x]) ans++; return ans;
}
```
