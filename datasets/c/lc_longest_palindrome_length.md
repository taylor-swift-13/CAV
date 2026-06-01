# LC Longest Palindrome Length

## Problem

Return the length of the longest palindromic contiguous substring of ASCII string `s`.

## Requirements

- The empty string returns `0`.
- Compare characters by byte value.
- Return only the length, not the substring itself.

## Source

- Source: LeetCode problem `longest-palindromic-substring`.
- URL: https://leetcode.com/problems/longest-palindromic-substring/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_longest_palindrome_length(const char *s) {
    int len = 0;
    while (s[len] != '\0') len++;
    int best = 0;
    for (int center = 0; center < len; center++) {
        int l = center, r = center;
        while (l >= 0 && r < len && s[l] == s[r]) {
            int size = r - l + 1;
            if (size > best) best = size;
            l--; r++;
        }
        l = center; r = center + 1;
        while (l >= 0 && r < len && s[l] == s[r]) {
            int size = r - l + 1;
            if (size > best) best = size;
            l--; r++;
        }
    }
    return best;
}
```
