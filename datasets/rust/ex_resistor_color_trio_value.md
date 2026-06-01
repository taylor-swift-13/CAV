# Exercism Resistor Color Trio Value

## Problem

Return the resistance value from two color digits and a multiplier digit.

## Requirements

- Colors are encoded as standard resistor-color digits `0..9`.
- The value is `(10*first + second) * 10^multiplier`.

## Source

- Source: Exercism problem `resistor-color-trio`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/resistor-color-trio
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_resistor_color_trio_value(first: i32, second: i32, multiplier: i32) -> i32 {
    let mut value = first * 10 + second; let mut i = 0; while i < multiplier { value *= 10; i += 1; } value
}
```
