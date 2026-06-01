# LC Valid Palindrome II Bool

## Problem

Return true if `s` can be a palindrome after deleting at most one character.

## Requirements

- Input is lowercase ASCII.

## Source

- Source: LeetCode problem `valid-palindrome-ii`.
- URL: https://leetcode.com/problems/valid-palindrome-ii/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
static int lc_vp2_range(const char *s, int l, int r) { while (l < r) { if (s[l] != s[r]) return 0; l++; r--; } return 1; }
int lc_valid_palindrome_ii_bool(const char *s) {
    int r = 0; while (s[r] != '\0') r++; r--;
    int l = 0; while (l < r) { if (s[l] != s[r]) return lc_vp2_range(s, l + 1, r) || lc_vp2_range(s, l, r - 1); l++; r--; }
    return 1;
}
```
