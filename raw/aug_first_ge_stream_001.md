# aug_first_ge_stream_001

## Problem

Return the first index whose encoded value is at least `-5` using a streaming/no-array implementation.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `find_first_equal`
- Variant kind: `first-index-ge-streaming-no-array`
- Constants: `{"i": 1, "implementation_strategy": "streaming-no-array", "threshold": -5}`

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
int aug_first_ge_stream_001(const char *nums) {
    int idx = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        if (sign * v >= -5) return idx;
        idx++;
        if (nums[i] == ',') i++;
    }
    return -1;
}
```
