# single_number_csv

## Problem

In a comma-separated integer array where every value appears twice except one, return the single value.

## Requirements

- Input is nonempty.
- Exactly one value appears once and every other value appears twice.
- Values are base-10 integers with no spaces.
- Return the unique value.

## Source

- Source: LeetCode problem `single-number`.
- URL: https://leetcode.com/problems/single-number/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int single_number_csv(const char *nums) {
    int x = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; }
        x ^= sign * v;
        if (nums[i] == ',') i++;
    }
    return x;
}
```
