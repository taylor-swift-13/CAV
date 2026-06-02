# LC Palindromic Substrings Count

## Problem

Return the number of palindromic substrings of `s`.

## Requirements

- `s` contains lowercase English letters.

## Source

- Source: LeetCode problem `palindromic-substrings`.
- URL: https://leetcode.com/problems/palindromic-substrings/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_palindromic_substrings_count(const char *s) {
    int n = 0; while (s[n] != '\0') n++; int ans = 0; for (int center = 0; center < 2 * n - 1; center++) { int l = center / 2, r = l + center % 2; while (l >= 0 && r < n && s[l] == s[r]) { ans++; l--; r++; } } return ans;
}
```
