# xor_operation_array

## Problem

Build `nums[i] = start + 2*i` for `0 <= i < n` and return the XOR of all values.

## Requirements

- `n >= 1`.
- The generated array has exactly `n` values.
- The `i`th value is `start + 2*i`.
- Return bitwise XOR of all generated values.

## Source

- Source: LeetCode problem `xor-operation-in-an-array`.
- URL: https://leetcode.com/problems/xor-operation-in-an-array/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn xor_operation_array(n: i32, start: i32) -> i32 {
    let mut x = 0;
    let mut i = 0;
    while i < n { x ^= start + 2 * i; i += 1; }
    x
}
```
