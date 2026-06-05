# valid_palindrome_ascii

## Problem

Return true if ASCII string `s` is a palindrome after ignoring non-alphanumeric characters and case.

## Requirements

- `s` contains only ASCII characters for this dataset variant.
- Ignore every character that is not `[A-Za-z0-9]`.
- Letter comparison is case-insensitive; digit comparison is exact.
- The empty filtered string is a palindrome and must return true.
- The original string must not be modified.

## Source

- Source: LeetCode problem `valid-palindrome`.
- URL: https://leetcode.com/problems/valid-palindrome/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int valid_palindrome_ascii(const char *s) {
    int r = 0;
    while (s[r] != '\0') r++;
    int l = 0;
    r--;
    while (l < r) {
        char a = s[l];
        char b = s[r];
        int aa = (a >= '0' && a <= '9') || (a >= 'A' && a <= 'Z') || (a >= 'a' && a <= 'z');
        int bb = (b >= '0' && b <= '9') || (b >= 'A' && b <= 'Z') || (b >= 'a' && b <= 'z');
        if (!aa) { l++; continue; }
        if (!bb) { r--; continue; }
        if (a >= 'A' && a <= 'Z') a = (char)(a - 'A' + 'a');
        if (b >= 'A' && b <= 'Z') b = (char)(b - 'A' + 'a');
        if (a != b) return 0;
        l++;
        r--;
    }
    return 1;
}
```
