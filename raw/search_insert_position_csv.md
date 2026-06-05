# search_insert_position_csv

## Problem

Given a sorted comma-separated integer array `nums`, return the index of `target` or where it should be inserted.

## Requirements

- `nums` is sorted in strictly increasing order.
- The empty string represents an empty array.
- Return the first index whose value is at least `target`.
- If all values are smaller, return the array length.

## Source

- Source: LeetCode problem `search-insert-position`.
- URL: https://leetcode.com/problems/search-insert-position/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int search_insert_position_csv(const char *nums, int target) {
    int index = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        v *= sign;
        if (v >= target) return index;
        index++;
        if (nums[i] == ',') i++;
    }
    return index;
}
```
