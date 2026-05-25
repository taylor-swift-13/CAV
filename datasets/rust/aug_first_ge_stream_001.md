# aug_first_ge_stream_001

## Problem

Return the first index whose encoded value is at least `-5` using a streaming/no-array implementation.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `find_first_equal`
- Variant kind: `first-index-ge-streaming-no-array`
- Constants: `{"i": 1, "implementation_strategy": "streaming-no-array", "threshold": -5}`

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
pub fn aug_first_ge_stream_001(nums: &str) -> i32 {
    if nums.is_empty() { return -1; }
    for (i, p) in nums.split(',').enumerate() { if p.parse::<i32>().unwrap() >= -5 { return i as i32; } }
    -1
}
```
