# Exercism Hamming Distance

## Problem

Return the Hamming distance between equal-length strings `a` and `b`.

## Requirements

- Inputs have equal length.
- Strings are ASCII.

## Source

- Source: Exercism problem `hamming`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/hamming
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_hamming_distance(const char *a, const char *b) {
    int d = 0; for (int i = 0; a[i] != '\0'; i++) if (a[i] != b[i]) d++; return d;
}
```
