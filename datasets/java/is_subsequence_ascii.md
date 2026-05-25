# is_subsequence_ascii

## Problem

Return true if `s` is a subsequence of `t`.

## Requirements

- Inputs are ASCII strings.
- Characters must appear in the same order but need not be adjacent.
- The empty string is a subsequence of every string.
- Return false if `s` still has unmatched characters after scanning `t`.

## Source

- Source: LeetCode problem `is-subsequence`.
- URL: https://leetcode.com/problems/is-subsequence/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class IsSubsequenceAscii {
    public static boolean is_subsequence_ascii(String s, String t) {
        int i = 0;
        for (int j = 0; j < t.length() && i < s.length(); j++) if (s.charAt(i) == t.charAt(j)) i++;
        return i == s.length();
    }
}
```
