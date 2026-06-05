# Exercism ISBN Verifier Valid

## Problem

Return true if an ISBN-10 string has exactly 10 digits after hyphen removal and a valid checksum.

## Requirements

- Hyphens are ignored.
- `X` may appear only as the final check character and has value 10.

## Source

- Source: Exercism problem `isbn-verifier`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/isbn-verifier
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_isbn10_valid(const char *s) {
    int pos = 0, sum = 0;
    for (int i = 0; s[i] != '\0'; i++) { if (s[i] == '-') continue; int v; if (s[i] == 'X') { if (pos != 9) return 0; v = 10; } else if (s[i] >= '0' && s[i] <= '9') v = s[i] - '0'; else return 0; if (pos >= 10) return 0; sum += v * (10 - pos); pos++; }
    return pos == 10 && sum % 11 == 0;
}
```
