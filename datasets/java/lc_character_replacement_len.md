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

```java
class LcCharacterReplacementLen {
    public static int lc_character_replacement_len(String s, int k) {
        int[] cnt = new int[26]; int left = 0, maxc = 0, best = 0; for (int right = 0; right < s.length(); right++) { int idx = s.charAt(right) - 'A'; maxc = Math.max(maxc, ++cnt[idx]); while (right - left + 1 - maxc > k) cnt[s.charAt(left++) - 'A']--; best = Math.max(best, right - left + 1); } return best;
    }
}
```
