# running_sum_csv

## Problem

Return the running sum of comma-separated integer array `nums`.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Each output value is the sum from index `0` through that index.
- Return the output as comma-separated integers.

## Source

- Source: LeetCode problem `running-sum-of-1d-array`.
- URL: https://leetcode.com/problems/running-sum-of-1d-array/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
char *running_sum_csv(const char *nums) {
    char *out = (char *)malloc(512);
    int pos = 0, first = 1, sum = 0, i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        sum += sign * v;
        pos += sprintf(out + pos, "%s%d", first ? "" : ",", sum);
        first = 0;
        if (nums[i] == ',') i++;
    }
    out[pos] = '\0';
    return out;
}
```
