# merge_strings_alternately_ascii

## Problem

Merge `word1` and `word2` by alternating characters, starting with `word1`.

## Requirements

- Inputs are ASCII strings.
- Take one character from `word1`, then one from `word2`, repeatedly.
- Append the remaining suffix of the longer string.
- The empty string is allowed.

## Source

- Source: LeetCode problem `merge-strings-alternately`.
- URL: https://leetcode.com/problems/merge-strings-alternately/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class MergeStringsAlternatelyAscii {
    public static String merge_strings_alternately_ascii(String word1, String word2) {
        StringBuilder out = new StringBuilder();
        int limit = word1.length() > word2.length() ? word1.length() : word2.length();
        for (int i = 0; i < limit; i++) { if (i < word1.length()) out.append(word1.charAt(i)); if (i < word2.length()) out.append(word2.charAt(i)); }
        return out.toString();
    }
}
```
