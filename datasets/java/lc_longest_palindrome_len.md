# LC Longest Palindrome Length

## Problem

Return the length of the longest palindrome that can be built from the letters of `s`.

## Requirements

- Input is ASCII letters.

## Source

- Source: LeetCode problem `longest-palindrome`.
- URL: https://leetcode.com/problems/longest-palindrome/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLongestPalindromeLen {
    public static int lc_longest_palindrome_len(String s) {
        int[] cnt = new int[128]; for (int i = 0; i < s.length(); i++) cnt[s.charAt(i)]++; int ans = 0; boolean odd = false; for (int v : cnt) { ans += v / 2 * 2; if (v % 2 == 1) odd = true; } return ans + (odd ? 1 : 0);
    }
}
```
