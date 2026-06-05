# Exercism Raindrops Code

## Problem

Return a bitmask for raindrop sounds: bit 0 for factor 3, bit 1 for factor 5, bit 2 for factor 7.

## Requirements

- `n > 0`.
- This numeric code is a single-function rewrite of the raindrops exercise.

## Source

- Source: Exercism problem `raindrops`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/raindrops
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_raindrops_code(int n) {
    int code = 0;
    if (n % 3 == 0) code |= 1;
    if (n % 5 == 0) code |= 2;
    if (n % 7 == 0) code |= 4;
    return code;
}
```
