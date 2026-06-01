# LC Permutation In String Bool

## Problem

Return true if `s2` contains any permutation of `s1` as a substring.

## Requirements

- Both strings contain lowercase English letters.

## Source

- Source: LeetCode problem `permutation-in-string`.
- URL: https://leetcode.com/problems/permutation-in-string/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcPermutationInStringBool {
    public static boolean lc_permutation_in_string_bool(String s1, String s2) {
        int n = s1.length(), m = s2.length(); if (n > m) return false; int[] need = new int[26], win = new int[26]; for (int i = 0; i < n; i++) { need[s1.charAt(i) - 'a']++; win[s2.charAt(i) - 'a']++; } for (int i = 0; i <= m - n; i++) { if (java.util.Arrays.equals(need, win)) return true; if (i + n < m) { win[s2.charAt(i) - 'a']--; win[s2.charAt(i + n) - 'a']++; } } return false;
    }
}
```
