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

```java
class AugSumPrefixArray002 {
    public static int aug_sum_prefix_array_002(String nums) {
        String[] parts = nums.isEmpty() ? new String[0] : nums.split(",");
        int sum = 0;
        int stop = parts.length < 2 ? parts.length : 2;
        for (int j = 0; j < stop; j++) sum += Integer.parseInt(parts[j]);
        return sum;
    }
}
```
