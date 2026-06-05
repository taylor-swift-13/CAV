# LC Word Pattern Bool

## Problem

Return true if pattern letters bijectively match the words in `s`.

## Requirements

- Words in `s` are separated by single spaces.
- Pattern is lowercase ASCII.

## Source

- Source: LeetCode problem `word-pattern`.
- URL: https://leetcode.com/problems/word-pattern/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_word_pattern_bool(const char *pattern, const char *s) {
    char words[64][32]; int wn = 0, i = 0;
    while (s[i] != '\0') { int j = 0; while (s[i] != '\0' && s[i] != ' ') words[wn][j++] = s[i++]; words[wn][j] = '\0'; wn++; if (s[i] == ' ') i++; }
    int pn = 0; while (pattern[pn] != '\0') pn++; if (pn != wn) return 0;
    for (int a = 0; a < pn; a++) for (int b = a + 1; b < pn; b++) { int samep = pattern[a] == pattern[b]; int samew = 1; for (int k = 0; words[a][k] != '\0' || words[b][k] != '\0'; k++) if (words[a][k] != words[b][k]) samew = 0; if (samep != samew) return 0; }
    return 1;
}
```
