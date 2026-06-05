# aug_count_le_array_005

## Problem

Return how many comma-separated integers are at most `-4`.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `array_count_between`
- Variant kind: `threshold-count-le-array-backed`
- Constants: `{"i": 5, "implementation_strategy": "array-backed", "threshold": -4}`

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
int aug_count_le_array_005(const char *nums) {
    int values[64];
    int n = 0;
    int i = 0;
    while (nums[i] != '\0') {
        int sign = 1;
        if (nums[i] == '-') { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + (nums[i] - '0'); i++; }
        values[n] = sign * v; n++;
        if (nums[i] == ',') i++;
    }
    int count = 0;
    for (int j = 0; j < n; j++) if (values[j] <= -4) count++;
    return count;
}
```
