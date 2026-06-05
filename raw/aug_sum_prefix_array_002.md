# aug_sum_prefix_array_002

## Problem

Return the sum of the first `2` encoded integers, or fewer if the input is shorter.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `prefix_sum`
- Variant kind: `fixed-prefix-sum-array-backed`
- Constants: `{"i": 2, "implementation_strategy": "array-backed", "limit": 2}`

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
int aug_sum_prefix_array_002(const char *nums) {
    int values[64];
    int n = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; }
        values[n++] = sign * v;
        if (nums[i] == ',') i++;
    }
    int sum = 0;
    int stop = n < 2 ? n : 2;
    for (int j = 0; j < stop; j++) sum += values[j];
    return sum;
}
```
