# Exercism Nucleotide Count Char

## Problem

Return how many times nucleotide `target` appears in DNA string `dna`.

## Requirements

- `target` is a one-character string among `A,C,G,T`.
- `dna` contains only valid DNA nucleotides.

## Source

- Source: Exercism problem `nucleotide-count`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/nucleotide-count
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_nucleotide_count_char(dna: &str, target: &str) -> i32 {
    let t = target.as_bytes()[0]; let mut ans = 0; for ch in dna.bytes() { if ch == t { ans += 1; } } ans
}
```
