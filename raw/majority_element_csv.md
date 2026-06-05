# majority_element_csv

## Problem

Return the value that appears more than half the time in comma-separated integer string `nums`.

## Requirements

- `nums` is nonempty and comma-separated with no spaces.
- A majority element is guaranteed to exist.
- Return the element value.
- At most 64 integers are encoded.

## Source

- Source: LeetCode problem `majority-element`.
- URL: https://leetcode.com/problems/majority-element/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int majority_element_csv(const char *nums) {
    int candidate = 0;
    int count = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        v *= sign;
        if (count == 0) { candidate = v; count = 1; }
        else if (candidate == v) count++;
        else count--;
        if (nums[i] == ',') i++;
    }
    return candidate;
}
```
