# number_steps_reduce_zero

## Problem

Return the number of steps needed to reduce nonnegative integer `num` to zero. If it is even, divide by two; otherwise subtract one.

## Requirements

- `num >= 0`.
- An even positive number is divided by two.
- An odd positive number is decremented by one.
- Return the number of operations until zero.

## Source

- Source: LeetCode problem `number-of-steps-to-reduce-a-number-to-zero`.
- URL: https://leetcode.com/problems/number-of-steps-to-reduce-a-number-to-zero/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn number_steps_reduce_zero(mut num: i32) -> i32 {
    let mut steps = 0;
    while num > 0 { if num % 2 == 0 { num /= 2; } else { num -= 1; } steps += 1; }
    steps
}
```
