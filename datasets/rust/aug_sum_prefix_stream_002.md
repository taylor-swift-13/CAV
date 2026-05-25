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

```rust
pub fn aug_sum_prefix_stream_002(nums: &str) -> i32 {
    if nums.is_empty() { return 0; }
    nums.split(',').take(2).map(|p| p.parse::<i32>().unwrap()).sum()
}
```
