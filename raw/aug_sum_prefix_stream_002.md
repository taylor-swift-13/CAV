# aug_sum_prefix_stream_002

## Problem

Return the sum of the first `2` encoded integers using a streaming/no-array implementation.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `prefix_sum`
- Variant kind: `fixed-prefix-sum-streaming-no-array`
- Constants: `{"i": 2, "implementation_strategy": "streaming-no-array", "limit": 2}`

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
int aug_sum_prefix_stream_002(const char *nums) {
    int idx = 0;
    int sum = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        if (idx < 2) sum += sign * v;
        idx++;
        if (nums[i] == ',') i++;
    }
    return sum;
}
```
