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

```c
int ex_protein_stop_index(const char *rna) {
    int idx = 0;
    for (int i = 0; rna[i] != '\0'; i += 3) { if (rna[i] == 'U' && ((rna[i + 1] == 'A' && (rna[i + 2] == 'A' || rna[i + 2] == 'G')) || (rna[i + 1] == 'G' && rna[i + 2] == 'A'))) return idx; idx++; }
    return idx;
}
```
