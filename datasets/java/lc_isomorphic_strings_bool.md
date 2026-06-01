# LC Isomorphic Strings Bool

## Problem

Return true if two ASCII strings are isomorphic.

## Requirements

- Both strings have the same length.
- A bijection between characters must preserve order.

## Source

- Source: LeetCode problem `isomorphic-strings`.
- URL: https://leetcode.com/problems/isomorphic-strings/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcIsomorphicStringsBool {
    public static boolean lc_isomorphic_strings_bool(String s, String t) {
        int[] st = new int[256], ts = new int[256]; for (int i = 0; i < s.length(); i++) { int a = s.charAt(i), b = t.charAt(i); if (st[a] != ts[b]) return false; st[a] = i + 1; ts[b] = i + 1; } return true;
    }
}
```
