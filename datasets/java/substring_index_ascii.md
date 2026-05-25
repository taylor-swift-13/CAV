# substring_index_ascii

## Problem

Return the first index of `needle` in `haystack`, or `-1` if absent.

## Requirements

- Inputs are ASCII strings.
- Return a zero-based index.
- If `needle` is empty, return `0`.
- Use direct substring matching semantics.

## Source

- Source: LeetCode problem `find-the-index-of-the-first-occurrence-in-a-string`.
- URL: https://leetcode.com/problems/find-the-index-of-the-first-occurrence-in-a-string/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class SubstringIndexAscii {
    public static int substring_index_ascii(String haystack, String needle) {
        if (needle.isEmpty()) return 0;
        for (int i = 0; i + needle.length() <= haystack.length(); i++) {
            int ok = 1;
            for (int j = 0; j < needle.length(); j++) if (haystack.charAt(i + j) != needle.charAt(j)) ok = 0;
            if (ok == 1) return i;
        }
        return -1;
    }
}
```
