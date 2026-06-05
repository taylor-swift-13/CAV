# Exercism Pangram ASCII

## Problem

Return true if `s` contains every English letter at least once, ignoring case.

## Requirements

- Input is ASCII.
- Nonletters are ignored.

## Source

- Source: Exercism problem `pangram`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/pangram
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_pangram_ascii(const char *s) {
    int mask = 0;
    for (int i = 0; s[i] != '\0'; i++) { char c = s[i]; if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a'); if (c >= 'a' && c <= 'z') mask |= 1 << (c - 'a'); }
    return mask == ((1 << 26) - 1);
}
```
