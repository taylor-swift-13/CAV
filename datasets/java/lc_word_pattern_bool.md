# LC Word Pattern Bool

## Problem

Return true if pattern letters bijectively match the words in `s`.

## Requirements

- Words in `s` are separated by single spaces.
- Pattern is lowercase ASCII.

## Source

- Source: LeetCode problem `word-pattern`.
- URL: https://leetcode.com/problems/word-pattern/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcWordPatternBool {
    public static boolean lc_word_pattern_bool(String pattern, String s) {
        String[] w = s.split(" "); if (w.length != pattern.length()) return false; for (int i = 0; i < w.length; i++) for (int j = i + 1; j < w.length; j++) if ((pattern.charAt(i) == pattern.charAt(j)) != w[i].equals(w[j])) return false; return true;
    }
}
```
