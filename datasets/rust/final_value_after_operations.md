# final_value_after_operations

## Problem

Starting from zero, apply comma-separated operations `++X`, `X++`, `--X`, or `X--` and return the final value.

## Requirements

- `operations` is comma-separated with no spaces.
- Allowed operations are `++X`, `X++`, `--X`, and `X--`.
- Increment operations add one; decrement operations subtract one.
- The empty string represents no operations.

## Source

- Source: LeetCode problem `final-value-of-variable-after-performing-operations`.
- URL: https://leetcode.com/problems/final-value-of-variable-after-performing-operations/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn final_value_after_operations(operations: &str) -> i32 {
    if operations.is_empty() { return 0; }
    let mut value = 0;
    for op in operations.split(',') { let b = op.as_bytes(); if b[0] == b'+' || b[1] == b'+' { value += 1; } else { value -= 1; } }
    value
}
```
