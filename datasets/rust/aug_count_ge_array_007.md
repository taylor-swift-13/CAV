# aug_count_ge_array_007

## Problem

Return how many comma-separated integers are at least `-1`.

## Augment Metadata

- Parent dataset: `internal`
- Parent problem: `array_count_between`
- Variant kind: `threshold-count-ge-array-backed`
- Constants: `{"i": 7, "implementation_strategy": "array-backed", "threshold": -1}`

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
pub fn aug_count_ge_array_007(nums: &str) -> i32 {
    let values: Vec<i32> = if nums.is_empty() { Vec::new() } else { nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect() };
    values.iter().filter(|&&v| v >= -1).count() as i32
}
```
