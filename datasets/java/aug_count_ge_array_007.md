# aug_count_ge_array_007

## Problem

Return how many comma-separated integers are at least `-1`.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `array_count_between`
- Variant kind: `threshold-count-ge-array-backed`
- Constants: `{"i": 7, "implementation_strategy": "array-backed", "threshold": -1}`

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

```java
class AugCountGeArray007 {
    public static int aug_count_ge_array_007(String nums) {
        String[] parts = nums.isEmpty() ? new String[0] : nums.split(",");
        int count = 0;
        for (String p : parts) if (Integer.parseInt(p) >= -1) count++;
        return count;
    }
}
```
