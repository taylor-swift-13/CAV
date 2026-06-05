# aug_last_le_array_006

## Problem

Return the last index whose value is at most `1`, or `-1`.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `array_find_last_equal`
- Variant kind: `last-index-le-array-backed`
- Constants: `{"i": 6, "implementation_strategy": "array-backed", "threshold": 1}`

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
int aug_last_le_array_006(const char *nums) {
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
    int last = -1;
    for (int j = 0; j < n; j++) if (values[j] <= 1) last = j;
    return last;
}
```
