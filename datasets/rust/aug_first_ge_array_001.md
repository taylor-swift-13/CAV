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

```rust
pub fn aug_first_ge_array_001(nums: &str) -> i32 {
    let values: Vec<i32> = if nums.is_empty() { Vec::new() } else { nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect() };
    for i in 0..values.len() { if values[i] >= -5 { return i as i32; } }
    -1
}
```
