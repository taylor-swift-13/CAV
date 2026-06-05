# Exercism Luhn Valid ASCII

## Problem

Return true if `s` passes the Luhn checksum, ignoring spaces.

## Requirements

- Only digits and spaces are accepted.
- After removing spaces, length must be at least 2.

## Source

- Source: Exercism problem `luhn`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/luhn
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_luhn_valid_ascii(const char *s) {
    int digits[128], n = 0;
    for (int i = 0; s[i] != '\0'; i++) { if (s[i] == ' ') continue; if (s[i] < '0' || s[i] > '9') return 0; digits[n] = s[i] - '0'; n++; }
    if (n < 2) return 0;
    int sum = 0, dbl = 0;
    for (int i = n - 1; i >= 0; i--) { int v = digits[i]; if (dbl) { v *= 2; if (v > 9) v -= 9; } sum += v; dbl = !dbl; }
    return sum % 10 == 0;
}
```
