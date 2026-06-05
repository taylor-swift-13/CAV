# LC Minimum Window Substring Length

## Problem

Return the length of the shortest substring of `s` containing all characters of `t`, or `0` if none exists.

## Requirements

- Inputs are ASCII.
- Character multiplicity in `t` matters.

## Source

- Source: LeetCode problem `minimum-window-substring`.
- URL: https://leetcode.com/problems/minimum-window-substring/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_min_window_substring_len(const char *s, const char *t) {
    int need[128] = {0}, have[128] = {0}, required = 0; for (int i = 0; t[i] != '\0'; i++) { if (need[(int)t[i]] == 0) required++; need[(int)t[i]]++; }
    int formed = 0, left = 0, best = 1000000; for (int right = 0; s[right] != '\0'; right++) { int ch = (int)s[right]; have[ch]++; if (need[ch] > 0 && have[ch] == need[ch]) formed++; while (formed == required) { int len = right - left + 1; if (len < best) best = len; int lc = (int)s[left++]; if (need[lc] > 0 && have[lc] == need[lc]) formed--; have[lc]--; } } return best == 1000000 ? 0 : best;
}
```
