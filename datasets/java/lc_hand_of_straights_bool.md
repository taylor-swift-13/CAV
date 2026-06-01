# LC Hand Of Straights Bool

## Problem

Return true if the hand can be rearranged into groups of consecutive cards.

## Requirements

- `hand` is a comma-separated list of card values.
- `group_size > 0`.

## Source

- Source: LeetCode problem `hand-of-straights`.
- URL: https://leetcode.com/problems/hand-of-straights/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcHandOfStraightsBool {
    public static boolean lc_hand_of_straights_bool(String hand, int group_size) {
        String[] p = hand.split(","); if (p.length % group_size != 0) return false; int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.Arrays.sort(a); boolean[] used = new boolean[a.length]; for (int i = 0; i < a.length; i++) if (!used[i]) { int need = a[i]; for (int g = 0; g < group_size; g++) { int found = -1; for (int j = 0; j < a.length; j++) if (!used[j] && a[j] == need) { found = j; break; } if (found < 0) return false; used[found] = true; need++; } } return true;
    }
}
```
