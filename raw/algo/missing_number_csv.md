# missing_number_csv

## Problem

Given `n` and a comma-separated list containing `n` distinct numbers from `0..n`, return the missing number.

## Requirements

- `n >= 1`.
- `nums` encodes exactly `n` distinct integers unless `n == 1` and the encoded list is empty.
- The represented set is a subset of `0..n` with one value missing.
- Return the missing value, not its position.

## Source

- Source: LeetCode problem `missing-number`.
- URL: https://leetcode.com/problems/missing-number/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int missing_number_csv(int n, const char *nums) {
    int expected = n * (n + 1) / 2;
    int sum = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; }
        sum += v;
        if (nums[i] == ',') i++;
    }
    return expected - sum;
}
```
