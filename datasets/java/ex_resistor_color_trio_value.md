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

```java
class ExResistorColorTrioValue {
    public static int ex_resistor_color_trio_value(int first, int second, int multiplier) {
        int value = first * 10 + second; for (int i = 0; i < multiplier; i++) value *= 10; return value;
    }
}
```
