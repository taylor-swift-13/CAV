# rna_transcription

## Problem

Return the RNA complement of a DNA string using `G->C`, `C->G`, `T->A`, and `A->U`.

## Requirements

- Implement exactly the named function shown in the reference implementation.
- Use only the language standard library.
- The function must be deterministic and must not read stdin or write stdout.
- Inputs satisfy the stated problem preconditions; behavior outside those preconditions is intentionally unspecified.

## Source

- Source: Exercism practice exercise `rna-transcription`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/rna-transcription
- License note: prompt rewrite and implementations are local; upstream inspiration is Exercism MIT licensed.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
#include <stdlib.h>
char *rna_transcription(const char *dna) {
    int n = 0;
    while (dna[n] != '\0') n++;
    char *out = (char *)malloc((unsigned long)n + 1);
    for (int i = 0; i < n; i++) {
        if (dna[i] == 'G') out[i] = 'C';
        else if (dna[i] == 'C') out[i] = 'G';
        else if (dna[i] == 'T') out[i] = 'A';
        else out[i] = 'U';
    }
    out[n] = '\0';
    return out;
}
```
