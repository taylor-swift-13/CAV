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

```c
static void ex_anagram_counts(const char *s, int start, int end, int out[26]) { for (int i = 0; i < 26; i++) out[i] = 0; for (int i = start; i < end; i++) { char ch = s[i]; if (ch >= 'A' && ch <= 'Z') ch = ch - 'A' + 'a'; out[ch - 'a']++; } }
int ex_anagram_count(const char *subject, const char *candidates) {
    int sl = 0; while (subject[sl] != '\0') sl++; int base[26]; ex_anagram_counts(subject, 0, sl, base); int ans = 0, i = 0;
    while (candidates[i] != '\0') { int start = i; while (candidates[i] != '\0' && candidates[i] != ';') i++; int end = i, same = sl == end - start; for (int k = 0; same && k < sl; k++) { char a = subject[k], b = candidates[start + k]; if (a >= 'A' && a <= 'Z') a = a - 'A' + 'a'; if (b >= 'A' && b <= 'Z') b = b - 'A' + 'a'; if (a != b) same = 0; } int cur[26]; ex_anagram_counts(candidates, start, end, cur); int ok = !same; for (int k = 0; k < 26; k++) if (base[k] != cur[k]) ok = 0; if (ok) ans++; if (candidates[i] == ';') i++; }
    return ans;
}
```
