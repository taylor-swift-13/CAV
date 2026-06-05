# two_sum_exists

## Problem

Return true if two distinct elements in integer array string `nums` sum to `target`.

## Requirements

- `nums` is encoded as comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- A valid pair must use two distinct positions, even if the values are equal.
- Return only whether such a pair exists; do not return indices.
- The number of encoded integers is at most 64 in this dataset variant.

## Source

- Source: LeetCode problem `two-sum`.
- URL: https://leetcode.com/problems/two-sum/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int two_sum_exists(const char *nums, int target) {
    int values[64];
    int n = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; }
        values[n++] = sign * v;
        if (nums[i] == ',') i++;
    }
    for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) if (values[a] + values[b] == target) return 1;
    return 0;
}
```
