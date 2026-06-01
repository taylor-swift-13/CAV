# LC Palindromic Substrings Count

## Problem

Return the number of palindromic substrings of `s`.

## Requirements

- `s` contains lowercase English letters.

## Source

- Source: LeetCode problem `palindromic-substrings`.
- URL: https://leetcode.com/problems/palindromic-substrings/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcPalindromicSubstringsCount {
    public static int lc_palindromic_substrings_count(String s) {
        int ans = 0; for (int center = 0; center < 2 * s.length() - 1; center++) { int l = center / 2, r = l + center % 2; while (l >= 0 && r < s.length() && s.charAt(l) == s.charAt(r)) { ans++; l--; r++; } } return ans;
    }
}
```
