# LC Minimum Deletions Unique Frequencies

## Problem

Return the minimum deletions needed so every nonzero character frequency is unique.

## Requirements

- `s` contains lowercase English letters.

## Source

- Source: LeetCode problem `minimum-deletions-to-make-character-frequencies-unique`.
- URL: https://leetcode.com/problems/minimum-deletions-to-make-character-frequencies-unique/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMinDeletionsUniqueFreq {
    public static int lc_min_deletions_unique_freq(String s) {
        int[] cnt = new int[26]; for (int i = 0; i < s.length(); i++) cnt[s.charAt(i) - 'a']++; boolean[] used = new boolean[s.length() + 1]; int del = 0; for (int f : cnt) { while (f > 0 && used[f]) { f--; del++; } if (f > 0) used[f] = true; } return del;
    }
}
```
