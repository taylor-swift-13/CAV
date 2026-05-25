# leap_year

## Problem

Return true if `year` is a leap year in the Gregorian calendar.

## Requirements

- Implement exactly the named function shown in the reference implementation.
- Use only the language standard library.
- The function must be deterministic and must not read stdin or write stdout.
- Inputs satisfy the stated problem preconditions; behavior outside those preconditions is intentionally unspecified.

## Source

- Source: Exercism practice exercise `leap`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/leap
- License note: prompt rewrite and implementations are local; upstream inspiration is Exercism MIT licensed.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn leap_year(year: i32) -> bool {
    if year % 400 == 0 { return true; }
    if year % 100 == 0 { return false; }
    year % 4 == 0
}
```
