# valid_palindrome_ascii

## Problem

Return true if ASCII string `s` is a palindrome after ignoring non-alphanumeric characters and case.

## Requirements

- `s` contains only ASCII characters for this dataset variant.
- Ignore every character that is not `[A-Za-z0-9]`.
- Letter comparison is case-insensitive; digit comparison is exact.
- The empty filtered string is a palindrome and must return true.
- The original string must not be modified.

## Source

- Source: LeetCode problem `valid-palindrome`.
- URL: https://leetcode.com/problems/valid-palindrome/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ValidPalindromeAscii {
    public static boolean valid_palindrome_ascii(String s) {
        int l = 0;
        int r = s.length() - 1;
        while (l < r) {
            char a = s.charAt(l);
            char b = s.charAt(r);
            if (!Character.isLetterOrDigit(a)) { l++; continue; }
            if (!Character.isLetterOrDigit(b)) { r--; continue; }
            if (Character.toLowerCase(a) != Character.toLowerCase(b)) return false;
            l++;
            r--;
        }
        return true;
    }
}
```
