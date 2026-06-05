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

```java
class LcMinWindowSubstringLen {
    public static int lc_min_window_substring_len(String s, String t) {
        int[] need = new int[128], have = new int[128]; int required = 0; for (int i = 0; i < t.length(); i++) { int ch = t.charAt(i); if (need[ch] == 0) required++; need[ch]++; } int formed = 0, left = 0, best = 1000000; for (int right = 0; right < s.length(); right++) { int ch = s.charAt(right); have[ch]++; if (need[ch] > 0 && have[ch] == need[ch]) formed++; while (formed == required) { best = Math.min(best, right - left + 1); int lc = s.charAt(left++); if (need[lc] > 0 && have[lc] == need[lc]) formed--; have[lc]--; } } return best == 1000000 ? 0 : best;
    }
}
```
