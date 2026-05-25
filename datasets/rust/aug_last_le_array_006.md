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

```rust
pub fn aug_last_le_array_006(nums: &str) -> i32 {
    let values: Vec<i32> = if nums.is_empty() { Vec::new() } else { nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect() };
    let mut last = -1;
    for i in 0..values.len() { if values[i] <= 1 { last = i as i32; } }
    last
}
```
