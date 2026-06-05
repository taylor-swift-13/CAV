# LC Minimum Deletions Unique Frequencies

## Problem

Return the minimum deletions needed so every nonzero character frequency is unique.

## Requirements

- `s` contains lowercase English letters.

## Source

- Source: LeetCode problem `minimum-deletions-to-make-character-frequencies-unique`.
- URL: https://leetcode.com/problems/minimum-deletions-to-make-character-frequencies-unique/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_min_deletions_unique_freq(const char *s) {
    int cnt[26] = {0}; for (int i = 0; s[i] != '\0'; i++) cnt[s[i] - 'a']++; int used[512] = {0}, del = 0; for (int i = 0; i < 26; i++) { int f = cnt[i]; while (f > 0 && used[f]) { f--; del++; } if (f > 0) used[f] = 1; } return del;
}
```
