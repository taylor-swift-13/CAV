# Exercism Resistor Color Duo Value

## Problem

Return the two-digit resistor value formed by the first two color codes.

## Requirements

- Colors are encoded as digits `0..9` in the standard resistor-color order.
- The result is `10 * first + second`.

## Source

- Source: Exercism problem `resistor-color-duo`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/resistor-color-duo
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_resistor_color_duo_value(int first, int second) {
    return first * 10 + second;
}
```
