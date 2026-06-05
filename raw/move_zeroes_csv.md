# move_zeroes_csv

## Problem

Move all zeroes in comma-separated integer array `nums` to the end while preserving nonzero order.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Preserve relative order of nonzero values.
- Return the transformed array encoding.

## Source

- Source: LeetCode problem `move-zeroes`.
- URL: https://leetcode.com/problems/move-zeroes/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
#include <stdlib.h>
#include <stdio.h>
char *move_zeroes_csv(const char *nums) {
    int values[128];
    int n = 0, i = 0;
    while (nums[i] != '\0') { int sign = 1; if (nums[i] == '-') { sign = -1; i++; } int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; } values[n++] = sign * v; if (nums[i] == ',') i++; }
    char *out = (char *)malloc(512);
    int pos = 0, first = 1, zeros = 0;
    for (int j = 0; j < n; j++) if (values[j] == 0) zeros++; else { pos += sprintf(out + pos, "%s%d", first ? "" : ",", values[j]); first = 0; }
    for (int j = 0; j < zeros; j++) { pos += sprintf(out + pos, "%s0", first ? "" : ","); first = 0; }
    out[pos] = '\0';
    return out;
}
```
