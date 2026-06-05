# LC Divide Two Integers Value

## Problem

Return integer quotient truncated toward zero with 32-bit overflow clamp.

## Requirements

- This preserves the original divide-two-integers result contract.

## Source

- Source: LeetCode problem `divide-two-integers`.
- URL: https://leetcode.com/problems/divide-two-integers/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_divide_two_integers_value(dividend: i32, divisor: i32) -> i32 {
    if dividend == i32::MIN && divisor == -1 { return i32::MAX; } dividend / divisor
}
```
