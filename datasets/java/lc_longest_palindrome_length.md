# LC Longest Palindrome Length

## Problem

Return the length of the longest palindromic contiguous substring of ASCII string `s`.

## Requirements

- The empty string returns `0`.
- Compare characters by byte value.
- Return only the length, not the substring itself.

## Source

- Source: LeetCode problem `longest-palindromic-substring`.
- URL: https://leetcode.com/problems/longest-palindromic-substring/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLongestPalindromeLength {
    public static int lc_longest_palindrome_length(String s) {
        int best = 0;
        for (int center = 0; center < s.length(); center++) {
            int l = center, r = center;
            while (l >= 0 && r < s.length() && s.charAt(l) == s.charAt(r)) {
                int size = r - l + 1;
                if (size > best) best = size;
                l--; r++;
            }
            l = center; r = center + 1;
            while (l >= 0 && r < s.length() && s.charAt(l) == s.charAt(r)) {
                int size = r - l + 1;
                if (size > best) best = size;
                l--; r++;
            }
        }
        return best;
    }
}
```
