# first_unique_char_index

## Problem

Return the index of the first non-repeating lowercase letter in `s`, or `-1` if none exists.

## Requirements

- `s` contains only lowercase English letters.
- Return a zero-based index.
- If all characters repeat, return `-1`.
- The empty string is outside this task.

## Source

- Source: LeetCode problem `first-unique-character-in-a-string`.
- URL: https://leetcode.com/problems/first-unique-character-in-a-string/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FirstUniqueCharIndex {
    public static int first_unique_char_index(String s) {
        int[] count = new int[26];
        for (int i = 0; i < s.length(); i++) count[s.charAt(i) - 'a']++;
        for (int i = 0; i < s.length(); i++) if (count[s.charAt(i) - 'a'] == 1) return i;
        return -1;
    }
}
```
