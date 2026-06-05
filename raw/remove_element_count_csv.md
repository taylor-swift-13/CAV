# remove_element_count_csv

## Problem

Return how many values in comma-separated integer string `nums` are not equal to `val`.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Return only the kept length, not the reordered array.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `remove-element`.
- URL: https://leetcode.com/problems/remove-element/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int remove_element_count_csv(const char *nums, int val) {
    int count = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        if (sign * v != val) count++;
        if (nums[i] == ',') i++;
    }
    return count;
}
```
