# LC Buddy Strings Bool

## Problem

Return true if swapping exactly two letters in `s` can make it equal to `goal`.

## Requirements

- Inputs contain lowercase English letters.

## Source

- Source: LeetCode problem `buddy-strings`.
- URL: https://leetcode.com/problems/buddy-strings/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_buddy_strings_bool(const char *s, const char *goal) {
    int n = 0, m = 0; while (s[n] != '\0') n++; while (goal[m] != '\0') m++; if (n != m) return 0; int diff[2], d = 0, cnt[26] = {0}, dup = 0;
    for (int i = 0; i < n; i++) { int idx = s[i] - 'a'; cnt[idx]++; if (cnt[idx] > 1) dup = 1; if (s[i] != goal[i]) { if (d >= 2) return 0; diff[d++] = i; } }
    if (d == 0) return dup;
    return d == 2 && s[diff[0]] == goal[diff[1]] && s[diff[1]] == goal[diff[0]];
}
```
