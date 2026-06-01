# LC Buddy Strings Bool

## Problem

Return true if swapping exactly two letters in `s` can make it equal to `goal`.

## Requirements

- Inputs contain lowercase English letters.

## Source

- Source: LeetCode problem `buddy-strings`.
- URL: https://leetcode.com/problems/buddy-strings/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcBuddyStringsBool {
    public static boolean lc_buddy_strings_bool(String s, String goal) {
        if (s.length() != goal.length()) return false; int[] diff = new int[2], cnt = new int[26]; int d = 0; boolean dup = false; for (int i = 0; i < s.length(); i++) { int idx = s.charAt(i) - 'a'; if (++cnt[idx] > 1) dup = true; if (s.charAt(i) != goal.charAt(i)) { if (d >= 2) return false; diff[d++] = i; } } if (d == 0) return dup; return d == 2 && s.charAt(diff[0]) == goal.charAt(diff[1]) && s.charAt(diff[1]) == goal.charAt(diff[0]);
    }
}
```
