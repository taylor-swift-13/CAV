# armstrong_number

## Problem

Return true if `n` equals the sum of its digits each raised to the number of digits.

## Requirements

- Implement exactly the named function shown in the reference implementation.
- Use only the language standard library.
- The function must be deterministic and must not read stdin or write stdout.
- Inputs satisfy the stated problem preconditions; behavior outside those preconditions is intentionally unspecified.

## Source

- Source: Exercism practice exercise `armstrong-numbers`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/armstrong-numbers
- License note: prompt rewrite and implementations are local; upstream inspiration is Exercism MIT licensed.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn armstrong_number(n: i32) -> bool {
    let mut temp = n;
    let mut digits = if temp == 0 { 1 } else { 0 };
    while temp > 0 { digits += 1; temp /= 10; }
    temp = n;
    let mut sum = 0;
    while temp > 0 {
        let d = temp % 10;
        let mut p = 1;
        let mut i = 0;
        while i < digits { p *= d; i += 1; }
        sum += p;
        temp /= 10;
    }
    sum == n
}
```
