# LC Longest Consecutive Sequence Length CSV

## Problem

Return the length of the longest consecutive integer run in a comma-separated list.

## Requirements

- The empty string returns `0`.
- Duplicate values do not extend a run.

## Source

- Source: LeetCode problem `longest-consecutive-sequence`.
- URL: https://leetcode.com/problems/longest-consecutive-sequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_longest_consecutive_len_csv(const char *nums) {
    if (nums[0] == '\0') return 0;
    int a[256], n = 0, i = 0;
    while (nums[i] != '\0') { int sign = 1, v = 0; if (nums[i] == '-') { sign = -1; i++; } while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } a[n] = sign * v; n++; if (nums[i] == ',') i++; }
    for (int x = 0; x < n; x++) for (int y = x + 1; y < n; y++) if (a[y] < a[x]) { int t = a[x]; a[x] = a[y]; a[y] = t; }
    int best = 1, cur = 1; for (int x = 1; x < n; x++) { if (a[x] == a[x - 1]) continue; if (a[x] == a[x - 1] + 1) cur++; else cur = 1; if (cur > best) best = cur; }
    return best;
}
```
