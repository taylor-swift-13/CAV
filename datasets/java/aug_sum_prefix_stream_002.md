# aug_sum_prefix_stream_002

## Problem

Return the sum of the first `2` encoded integers using a streaming/no-array implementation.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `prefix_sum`
- Variant kind: `fixed-prefix-sum-streaming-no-array`
- Constants: `{"i": 2, "implementation_strategy": "streaming-no-array", "limit": 2}`

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
class AugSumPrefixStream002 {
    public static int aug_sum_prefix_stream_002(String nums) {
        int idx = 0, sum = 0, i = 0;
        while (i < nums.length()) {
            int sign = 1;
            if (nums.charAt(i) == '-') { sign = -1; i++; }
            int v = 0;
            while (i < nums.length() && nums.charAt(i) >= '0' && nums.charAt(i) <= '9') { v = v * 10 + nums.charAt(i) - '0'; i++; }
            if (idx < 2) sum += sign * v;
            idx++;
            if (i < nums.length() && nums.charAt(i) == ',') i++;
        }
        return sum;
    }
}
```
