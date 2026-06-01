# Exercism Pythagorean Triplet Product

## Problem

Return the product `a*b*c` for the first Pythagorean triplet with `a < b < c` and `a+b+c == sum`, or `0` if none exists.

## Requirements

- `sum > 0`.
- The product fits in signed 32-bit integer range.

## Source

- Source: Exercism problem `pythagorean-triplet`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/pythagorean-triplet
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_pythagorean_triplet_product(sum: i32) -> i32 {
    let mut a = 1;
    while a < sum { let mut b = a + 1; while b < sum { let c = sum - a - b; if b < c && a * a + b * b == c * c { return a * b * c; } b += 1; } a += 1; }
    0
}
```
