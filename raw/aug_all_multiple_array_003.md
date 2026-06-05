# aug_all_multiple_array_003

## Problem

Return true if every encoded integer is divisible by `5`. The empty array returns true.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `array_all_even`
- Variant kind: `fixed-divisibility-all-array-backed`
- Constants: `{"i": 3, "implementation_strategy": "array-backed", "mod": 5}`

## Signature

- Return: `bool`
- Params: `nums:string`

## Requirements

- Implement exactly the named function.
- Use only the language standard library.
- Do not read stdin or write stdout.
- Inputs satisfy the stated encoding constraints.
- This is an augment item: it is a same-problem implementation variant or a small semantic variant of the recorded parent problem.

## Reference Implementation

```c
int aug_all_multiple_array_003(const char *nums) {
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
    for (int j = 0; j < n; j++) if (values[j] % 5 != 0) return 0;
    return 1;
}
```
