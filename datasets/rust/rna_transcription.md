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

```rust
pub fn rna_transcription(dna: &str) -> String {
    let mut out = String::new();
    for c in dna.chars() {
        if c == 'G' { out.push('C'); }
        else if c == 'C' { out.push('G'); }
        else if c == 'T' { out.push('A'); }
        else { out.push('U'); }
    }
    out
}
```
