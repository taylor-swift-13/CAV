# array_min_csv

## Problem

Return the minimum value in nonempty comma-separated integer string `nums`.

## Requirements

- `nums` is nonempty and comma-separated with no spaces.
- Return the smallest integer value.
- Negative numbers are allowed.
- At most 64 integers are encoded.

## Source

- Source: FormalBench-inspired program `array-min`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int array_min_csv(const char *nums) {
    int i = 0;
    int sign = 1;
    if (nums[i] == '-') { sign = -1; i++; }
    int best = 0;
    while (nums[i] >= '0' && nums[i] <= '9') { best = best * 10 + nums[i] - '0'; i++; }
    best *= sign;
    if (nums[i] == ',') i++;
    while (nums[i] != '\0') {
        sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        v *= sign;
        if (v < best) best = v;
        if (nums[i] == ',') i++;
    }
    return best;
}
```
