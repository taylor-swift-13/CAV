# gcd_positive

## Problem

Return the greatest common divisor of positive integers `a` and `b`.

## Requirements

- `a > 0` and `b > 0`; zero and negative inputs are outside this task.
- Return the largest positive integer that divides both inputs.
- When one input divides the other, return the smaller divisor.
- The implementation must be iterative or otherwise guaranteed to terminate on 32-bit positive inputs.

## Source

- Source: local simple-function seed `gcd-positive`.
- URL: local dataset seed, no upstream problem URL.
- License note: prompt and implementation are local to this repository.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn gcd_positive(mut a: i32, mut b: i32) -> i32 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
```
