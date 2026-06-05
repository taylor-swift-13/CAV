# valid_anagram_ascii

## Problem

Return true if lowercase strings `a` and `b` are anagrams of each other.

## Requirements

- Inputs contain lowercase English letters only.
- The empty string is allowed.
- Return true exactly when both strings contain each letter the same number of times.
- No sorting is required.

## Source

- Source: LeetCode problem `valid-anagram`.
- URL: https://leetcode.com/problems/valid-anagram/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int valid_anagram_ascii(const char *a, const char *b) {
    int count[26] = {0};
    int i = 0;
    while (a[i] != '\0') { count[a[i] - 'a']++; i++; }
    i = 0;
    while (b[i] != '\0') { count[b[i] - 'a']--; i++; }
    for (i = 0; i < 26; i++) if (count[i] != 0) return 0;
    return 1;
}
```
