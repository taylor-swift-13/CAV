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

```java
class AugFirstGeArray001 {
    public static int aug_first_ge_array_001(String nums) {
        String[] parts = nums.isEmpty() ? new String[0] : nums.split(",");
        for (int j = 0; j < parts.length; j++) if (Integer.parseInt(parts[j]) >= -5) return j;
        return -1;
    }
}
```
