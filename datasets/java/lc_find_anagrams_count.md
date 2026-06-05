# LC Find All Anagrams Count

## Problem

Return how many start positions in `s` are anagrams of `p`.

## Requirements

- `s` and `p` contain lowercase English letters.

## Source

- Source: LeetCode problem `find-all-anagrams-in-a-string`.
- URL: https://leetcode.com/problems/find-all-anagrams-in-a-string/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcFindAnagramsCount {
    public static int lc_find_anagrams_count(String s, String p) {
        int n = s.length(), m = p.length(); if (m > n) return 0; int[] need = new int[26], win = new int[26]; for (int i = 0; i < m; i++) { need[p.charAt(i) - 'a']++; win[s.charAt(i) - 'a']++; } int ans = 0; for (int i = 0; i <= n - m; i++) { if (java.util.Arrays.equals(need, win)) ans++; if (i + m < n) { win[s.charAt(i) - 'a']--; win[s.charAt(i + m) - 'a']++; } } return ans;
    }
}
```
