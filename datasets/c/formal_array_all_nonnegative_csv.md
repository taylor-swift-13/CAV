# formal_array_all_nonnegative_csv

## Problem

Return true if every value in comma-separated integer array `nums` is nonnegative.

## Requirements

- The empty array is considered all nonnegative.
- Values are comma-separated with no spaces.
- Zero is nonnegative.
- Return false if any value is below zero.

## Source

- Source: FormalBench-inspired program `array-all-nonnegative`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int formal_array_all_nonnegative_csv(const char *nums) {
    int i = 0;
    while (nums[i] != '\0') { int sign = 1; if (nums[i] == '-') { sign = -1; i++; } int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } if (sign * v < 0) return 0; if (nums[i] == ',') i++; }
    return 1;
}
```
