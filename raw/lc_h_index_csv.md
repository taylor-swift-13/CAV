# LC H Index CSV

## Problem

Return the H-index for comma-separated citation counts.

## Requirements

- `citations` is a nonempty comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `h-index`.
- URL: https://leetcode.com/problems/h-index/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_h_index_csv(const char *citations) {
    int a[256], n = 0, i = 0; while (citations[i] != '\0') { int v = 0; while (citations[i] >= '0' && citations[i] <= '9') { v = v * 10 + citations[i] - '0'; i++; } a[n++] = v; if (citations[i] == ',') i++; }
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; }
    int h = 0; for (int x = 0; x < n; x++) { int cand = n - x; if (a[x] >= cand && cand > h) h = cand; } return h;
}
```
