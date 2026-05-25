# aug_count_ge_stream_007

## Problem

Return how many comma-separated integers are at least `-1` using a streaming/no-array implementation.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `array_count_between`
- Variant kind: `threshold-count-ge-streaming-no-array`
- Constants: `{"i": 7, "implementation_strategy": "streaming-no-array", "threshold": -1}`

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
pub fn aug_count_ge_stream_007(nums: &str) -> i32 {
    if nums.is_empty() { return 0; }
    let mut count = 0;
    for p in nums.split(',') { if p.parse::<i32>().unwrap() >= -1 { count += 1; } }
    count
}
```
