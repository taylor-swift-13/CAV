# LC Ransom Note Bool

## Problem

Return true if `ransom` can be constructed from letters in `magazine`.

## Requirements

- Inputs contain lowercase English letters.

## Source

- Source: LeetCode problem `ransom-note`.
- URL: https://leetcode.com/problems/ransom-note/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_ransom_note_bool(const char *ransom, const char *magazine) {
    int cnt[26] = {0}; for (int i = 0; magazine[i] != '\0'; i++) cnt[magazine[i] - 'a']++; for (int i = 0; ransom[i] != '\0'; i++) if (--cnt[ransom[i] - 'a'] < 0) return 0; return 1;
}
```
