# LC Valid Palindrome II Bool

## Problem

Return true if `s` can be a palindrome after deleting at most one character.

## Requirements

- Input is lowercase ASCII.

## Source

- Source: LeetCode problem `valid-palindrome-ii`.
- URL: https://leetcode.com/problems/valid-palindrome-ii/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcValidPalindromeIiBool {
    static boolean ok(String s, int l, int r) { while (l < r) { if (s.charAt(l++) != s.charAt(r--)) return false; } return true; }
    public static boolean lc_valid_palindrome_ii_bool(String s) {
        int l = 0, r = s.length() - 1; while (l < r) { if (s.charAt(l) != s.charAt(r)) return ok(s, l + 1, r) || ok(s, l, r - 1); l++; r--; } return true;
    }
}
```
