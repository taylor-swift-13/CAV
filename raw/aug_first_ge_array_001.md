# aug_first_ge_array_001

## Problem

Return the first index whose value is at least `-5`, or `-1`.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `find_first_equal`
- Variant kind: `first-index-ge-array-backed`
- Constants: `{"i": 1, "implementation_strategy": "array-backed", "threshold": -5}`

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
int aug_first_ge_array_001(const char *nums) {
    int values[64];
    int n = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; }
        values[n++] = sign * v;
        if (nums[i] == ',') i++;
    }
    for (int j = 0; j < n; j++) if (values[j] >= -5) return j;
    return -1;
}
```
