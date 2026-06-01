# Exercism Protein Stop Index

## Problem

Return the zero-based codon index of the first stop codon in an RNA string, or the number of codons if no stop codon appears.

## Requirements

- RNA length is a multiple of 3.
- Stop codons are `UAA`, `UAG`, and `UGA`.

## Source

- Source: Exercism problem `protein-translation`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/protein-translation
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_protein_stop_index(rna: &str) -> i32 {
    let b = rna.as_bytes(); let mut idx = 0; let mut i = 0usize;
    while i < b.len() { if b[i] == b'U' && ((b[i + 1] == b'A' && (b[i + 2] == b'A' || b[i + 2] == b'G')) || (b[i + 1] == b'G' && b[i + 2] == b'A')) { return idx; } idx += 1; i += 3; }
    idx
}
```
