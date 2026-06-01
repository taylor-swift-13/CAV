# Luogu P5714 BMI Category

## Problem

Return BMI category code for mass `m` kilograms and height `h` centimeters.

## Requirements

- `m > 0` and `h > 0`.
- Use BMI `m / meters^2`.
- Return `0` for underweight, `1` for normal, `2` for overweight.

## Source

- Source: Luogu problem `P5714`.
- URL: https://www.luogu.com.cn/problem/P5714
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5714_bmi_category(m: i32, h: i32) -> i32 {
    let bmi100 = m * 1000000 / (h * h);
    if bmi100 < 1850 { return 0; }
    if bmi100 < 2400 { return 1; }
    2
}
```
