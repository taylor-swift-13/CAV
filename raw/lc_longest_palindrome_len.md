# LC Longest Palindrome Length

## Problem

Return the length of the longest palindrome that can be built from the letters of `s`.

## Requirements

- Input is ASCII letters.

## Source

- Source: LeetCode problem `longest-palindrome`.
- URL: https://leetcode.com/problems/longest-palindrome/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_longest_palindrome_len(const char *s) {
    int cnt[128] = {0}; for (int i = 0; s[i] != '\0'; i++) cnt[(int)s[i]]++; int ans = 0, odd = 0; for (int i = 0; i < 128; i++) { ans += cnt[i] / 2 * 2; if (cnt[i] % 2) odd = 1; } return ans + odd;
}
```
