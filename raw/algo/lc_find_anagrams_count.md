# LC Find All Anagrams Count

## Problem

Return how many start positions in `s` are anagrams of `p`.

## Requirements

- `s` and `p` contain lowercase English letters.

## Source

- Source: LeetCode problem `find-all-anagrams-in-a-string`.
- URL: https://leetcode.com/problems/find-all-anagrams-in-a-string/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_find_anagrams_count(const char *s, const char *p) {
    int n = 0, m = 0; while (s[n] != '\0') n++; while (p[m] != '\0') m++; if (m > n) return 0; int need[26] = {0}, win[26] = {0}, ans = 0; for (int i = 0; i < m; i++) { need[p[i] - 'a']++; win[s[i] - 'a']++; } for (int i = 0; i <= n - m; i++) { int ok = 1; for (int c = 0; c < 26; c++) if (need[c] != win[c]) ok = 0; if (ok) ans++; if (i + m < n) { win[s[i] - 'a']--; win[s[i + m] - 'a']++; } } return ans;
}
```
