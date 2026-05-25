# formal_count_positive_csv

## Problem

Return how many values in comma-separated integer array `nums` are strictly positive.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Zero is not positive.
- Return the count of strictly positive values.

## Source

- Source: FormalBench-inspired program `count-positive`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int formal_count_positive_csv(const char *nums) {
    int count = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        if (sign * v > 0) count++;
        if (nums[i] == ',') i++;
    }
    return count;
}
```
