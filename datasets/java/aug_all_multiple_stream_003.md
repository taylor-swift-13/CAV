# aug_all_multiple_stream_003

## Problem

Return true if every encoded integer is divisible by `5` using a streaming/no-array implementation.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `array_all_even`
- Variant kind: `fixed-divisibility-all-streaming-no-array`
- Constants: `{"i": 3, "implementation_strategy": "streaming-no-array", "mod": 5}`

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
class AugAllMultipleStream003 {
    public static boolean aug_all_multiple_stream_003(String nums) {
        int i = 0;
        while (i < nums.length()) {
            int sign = 1;
            if (nums.charAt(i) == '-') { sign = -1; i++; }
            int v = 0;
            while (i < nums.length() && nums.charAt(i) >= '0' && nums.charAt(i) <= '9') { v = v * 10 + nums.charAt(i) - '0'; i++; }
            if ((sign * v) % 5 != 0) return false;
            if (i < nums.length() && nums.charAt(i) == ',') i++;
        }
        return true;
    }
}
```
