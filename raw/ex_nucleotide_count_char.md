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

```c
int ex_nucleotide_count_char(const char *dna, const char *target) {
    int ans = 0; for (int i = 0; dna[i] != '\0'; i++) if (dna[i] == target[0]) ans++; return ans;
}
```
