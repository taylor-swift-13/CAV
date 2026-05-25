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

```java
class AugAllMultipleArray003 {
    public static boolean aug_all_multiple_array_003(String nums) {
        String[] parts = nums.isEmpty() ? new String[0] : nums.split(",");
        for (String p : parts) if (Integer.parseInt(p) % 5 != 0) return false;
        return true;
    }
}
```
