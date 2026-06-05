# Exercism Isogram ASCII

## Problem

Return true if a phrase contains no repeated alphabetic letter, ignoring case and nonletters.

## Requirements

- Input is ASCII.
- Hyphens and spaces are ignored.

## Source

- Source: Exercism problem `isogram`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/isogram
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_isogram_ascii(const char *s) {
    int seen[26] = {0};
    for (int i = 0; s[i] != '\0'; i++) { char c = s[i]; if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a'); if (c >= 'a' && c <= 'z') { int k = c - 'a'; if (seen[k]) return 0; seen[k] = 1; } }
    return 1;
}
```
