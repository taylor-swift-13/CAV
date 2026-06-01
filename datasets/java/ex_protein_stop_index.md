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

```java
class ExProteinStopIndex {
    public static int ex_protein_stop_index(String rna) {
        int idx = 0;
        for (int i = 0; i < rna.length(); i += 3) { char a = rna.charAt(i), b = rna.charAt(i + 1), c = rna.charAt(i + 2); if (a == 'U' && ((b == 'A' && (c == 'A' || c == 'G')) || (b == 'G' && c == 'A'))) return idx; idx++; }
        return idx;
    }
}
```
