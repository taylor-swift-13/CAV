# contains_duplicate_csv

## Problem

Return true if comma-separated integer string `nums` contains the same value at least twice.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Return true if any two distinct positions contain equal values.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `contains-duplicate`.
- URL: https://leetcode.com/problems/contains-duplicate/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int contains_duplicate_csv(const char *nums) {
    int values[64];
    int n = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        values[n++] = sign * v;
        if (nums[i] == ',') i++;
    }
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (values[a] == values[b]) return 1;
    return 0;
}
```
