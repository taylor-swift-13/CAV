# valid_anagram_ascii

## Problem

Return true if lowercase strings `a` and `b` are anagrams of each other.

## Requirements

- Inputs contain lowercase English letters only.
- The empty string is allowed.
- Return true exactly when both strings contain each letter the same number of times.
- No sorting is required.

## Source

- Source: LeetCode problem `valid-anagram`.
- URL: https://leetcode.com/problems/valid-anagram/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ValidAnagramAscii {
    public static boolean valid_anagram_ascii(String a, String b) {
        int[] count = new int[26];
        for (int i = 0; i < a.length(); i++) count[a.charAt(i) - 'a']++;
        for (int i = 0; i < b.length(); i++) count[b.charAt(i) - 'a']--;
        for (int v : count) if (v != 0) return false;
        return true;
    }
}
```
