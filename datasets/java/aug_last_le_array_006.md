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

```java
class AugLastLeArray006 {
    public static int aug_last_le_array_006(String nums) {
        String[] parts = nums.isEmpty() ? new String[0] : nums.split(",");
        int last = -1;
        for (int j = 0; j < parts.length; j++) if (Integer.parseInt(parts[j]) <= 1) last = j;
        return last;
    }
}
```
