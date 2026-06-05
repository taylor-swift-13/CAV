# array_is_sorted_csv

## Problem

Return true if comma-separated integer string `nums` is sorted in nondecreasing order.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string is considered sorted.
- Duplicates are allowed.
- Return false on the first adjacent decrease.

## Source

- Source: FormalBench-inspired program `array-sorted`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int array_is_sorted_csv(const char *nums) {
    if (nums[0] == '\0') return 1;
    int i = 0;
    int sign = 1;
    if (nums[i] == '-') { sign = -1; i++; }
    int prev = 0;
    while (nums[i] >= '0' && nums[i] <= '9') { prev = prev * 10 + nums[i] - '0'; i++; }
    prev *= sign;
    if (nums[i] == ',') i++;
    while (nums[i] != '\0') {
        sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        v *= sign;
        if (v < prev) return 0;
        prev = v;
        if (nums[i] == ',') i++;
    }
    return 1;
}
```
