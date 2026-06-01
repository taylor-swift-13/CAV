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

```java
class ExIsogramAscii {
    public static boolean ex_isogram_ascii(String s) {
        boolean[] seen = new boolean[26];
        for (int i = 0; i < s.length(); i++) { char c = s.charAt(i); if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a'); if (c >= 'a' && c <= 'z') { int k = c - 'a'; if (seen[k]) return false; seen[k] = true; } }
        return true;
    }
}
```
