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

```c
int hamming_distance(const char *a, const char *b) {
    int count = 0;
    int i = 0;
    while (a[i] != '\0' && b[i] != '\0') {
        if (a[i] != b[i]) count++;
        i++;
    }
    return count;
}
```
