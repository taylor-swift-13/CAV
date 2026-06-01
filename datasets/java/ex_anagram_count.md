# Exercism Anagram Count

## Problem

Count candidate words that are anagrams of `subject` but not equal to it ignoring case.

## Requirements

- Candidates are separated by semicolons.
- Inputs are ASCII alphabetic words.

## Source

- Source: Exercism problem `anagram`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/anagram
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExAnagramCount {
    static int[] counts(String s) { int[] c = new int[26]; for (int i = 0; i < s.length(); i++) c[Character.toLowerCase(s.charAt(i)) - 'a']++; return c; }
    public static int ex_anagram_count(String subject, String candidates) {
        int[] base = counts(subject); String lower = subject.toLowerCase(); int ans = 0; for (String cand : candidates.split(";")) { if (cand.toLowerCase().equals(lower)) continue; int[] cur = counts(cand); boolean ok = true; for (int i = 0; i < 26; i++) if (base[i] != cur[i]) ok = false; if (ok) ans++; } return ans;
    }
}
```
