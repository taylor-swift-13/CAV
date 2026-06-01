# LC Ransom Note Bool

## Problem

Return true if `ransom` can be constructed from letters in `magazine`.

## Requirements

- Inputs contain lowercase English letters.

## Source

- Source: LeetCode problem `ransom-note`.
- URL: https://leetcode.com/problems/ransom-note/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcRansomNoteBool {
    public static boolean lc_ransom_note_bool(String ransom, String magazine) {
        int[] cnt = new int[26]; for (int i = 0; i < magazine.length(); i++) cnt[magazine.charAt(i) - 'a']++; for (int i = 0; i < ransom.length(); i++) if (--cnt[ransom.charAt(i) - 'a'] < 0) return false; return true;
    }
}
```
