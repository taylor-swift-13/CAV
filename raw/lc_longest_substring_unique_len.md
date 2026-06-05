# LC Longest Substring Unique Length

## Problem

Return the length of the longest substring of `s` without repeated ASCII characters.

## Requirements

- `s` is ASCII.
- The empty string returns `0`.

## Source

- Source: LeetCode problem `longest-substring-without-repeating-characters`.
- URL: https://leetcode.com/problems/longest-substring-without-repeating-characters/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_longest_substring_unique_len(const char *s) {
    int last[256];
    for (int i = 0; i < 256; i++) last[i] = -1;
    int left = 0, best = 0;
    for (int right = 0; s[right] != '\0'; right++) {
        unsigned char ch = (unsigned char)s[right];
        if (last[ch] >= left) left = last[ch] + 1;
        last[ch] = right;
        if (right - left + 1 > best) best = right - left + 1;
    }
    return best;
}
```
