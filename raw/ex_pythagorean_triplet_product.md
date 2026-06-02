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

```c
int ex_pythagorean_triplet_product(int sum) {
    for (int a = 1; a < sum; a++) for (int b = a + 1; b < sum; b++) { int c = sum - a - b; if (b < c && a * a + b * b == c * c) return a * b * c; }
    return 0;
}
```
