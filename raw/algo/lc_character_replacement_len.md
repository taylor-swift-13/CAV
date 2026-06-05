# LC Longest Repeating Character Replacement Length

## Problem

Return the longest substring length that can be made of one repeated character after at most `k` replacements.

## Requirements

- `s` contains uppercase English letters.
- `k >= 0`.

## Source

- Source: LeetCode problem `longest-repeating-character-replacement`.
- URL: https://leetcode.com/problems/longest-repeating-character-replacement/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_character_replacement_len(const char *s, int k) {
    int cnt[26] = {0}, left = 0, maxc = 0, best = 0; for (int right = 0; s[right] != '\0'; right++) { int idx = s[right] - 'A'; cnt[idx]++; if (cnt[idx] > maxc) maxc = cnt[idx]; while (right - left + 1 - maxc > k) { cnt[s[left] - 'A']--; left++; } int len = right - left + 1; if (len > best) best = len; } return best;
}
```
