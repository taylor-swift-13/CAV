# hamming_distance

## Problem

Return the number of positions where equal-length strings `a` and `b` differ.

## Requirements

- Implement exactly the named function shown in the reference implementation.
- Use only the language standard library.
- The function must be deterministic and must not read stdin or write stdout.
- Inputs satisfy the stated problem preconditions; behavior outside those preconditions is intentionally unspecified.

## Source

- Source: Exercism practice exercise `hamming`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/hamming
- License note: prompt rewrite and implementations are local; upstream inspiration is Exercism MIT licensed.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn hamming_distance(a: &str, b: &str) -> i32 {
    let ab = a.as_bytes();
    let bb = b.as_bytes();
    let mut count = 0;
    let mut i = 0;
    while i < ab.len() {
        if ab[i] != bb[i] { count += 1; }
        i += 1;
    }
    count
}
```
