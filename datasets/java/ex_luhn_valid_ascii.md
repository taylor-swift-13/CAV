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

```java
class ExLuhnValidAscii {
    public static boolean ex_luhn_valid_ascii(String s) {
        int[] digits = new int[128];
        int n = 0;
        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); if (c == ' ') continue; if (c < '0' || c > '9') return false; digits[n++] = c - '0'; }
        if (n < 2) return false;
        int sum = 0; boolean dbl = false;
        for (int i = n - 1; i >= 0; i--) { int v = digits[i]; if (dbl) { v *= 2; if (v > 9) v -= 9; } sum += v; dbl = !dbl; }
        return sum % 10 == 0;
    }
}
```
