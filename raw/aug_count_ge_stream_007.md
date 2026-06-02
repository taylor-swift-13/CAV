# aug_count_ge_stream_007

## Problem

Return how many comma-separated integers are at least `-1` using a streaming/no-array implementation.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `array_count_between`
- Variant kind: `threshold-count-ge-streaming-no-array`
- Constants: `{"i": 7, "implementation_strategy": "streaming-no-array", "threshold": -1}`

## Signature

- Return: `int`
- Params: `nums:string`

## Requirements

- Implement exactly the named function.
- Use only the language standard library.
- Do not read stdin or write stdout.
- Inputs satisfy the stated encoding constraints.
- This is an augment item: it is a same-problem implementation variant or a small semantic variant of the recorded parent problem.

## Reference Implementation

```c
int aug_count_ge_stream_007(const char *nums) {
    int count = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        if (sign * v >= -1) count++;
        if (nums[i] == ',') i++;
    }
    return count;
}
```
