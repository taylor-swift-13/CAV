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

```java
class ExIsbn10Valid {
    public static boolean ex_isbn10_valid(String s) {
        int pos = 0, sum = 0; for (int i = 0; i < s.length(); i++) { char ch = s.charAt(i); if (ch == '-') continue; int v; if (ch == 'X') { if (pos != 9) return false; v = 10; } else if (ch >= '0' && ch <= '9') v = ch - '0'; else return false; if (pos >= 10) return false; sum += v * (10 - pos); pos++; } return pos == 10 && sum % 11 == 0;
    }
}
```
