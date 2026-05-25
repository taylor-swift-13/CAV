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

```rust
pub fn aug_all_multiple_stream_003(nums: &str) -> bool {
    if nums.is_empty() { return true; }
    nums.split(',').all(|p| p.parse::<i32>().unwrap() % 5 == 0)
}
```
