# LC Palindrome Partitioning II Min Cut

## Problem

Return the minimum cuts needed so every substring part is a palindrome.

## Requirements

- `s` contains lowercase English letters.

## Source

- Source: LeetCode problem `palindrome-partitioning-ii`.
- URL: https://leetcode.com/problems/palindrome-partitioning-ii/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcPalPartitionMinCut {
    public static int lc_pal_partition_min_cut(String s) {
        int n = s.length(); boolean[][] pal = new boolean[n][n]; int[] cut = new int[n]; for (int i = 0; i < n; i++) cut[i] = i; for (int r = 0; r < n; r++) for (int l = r; l >= 0; l--) if (s.charAt(l) == s.charAt(r) && (r - l < 2 || pal[l + 1][r - 1])) { pal[l][r] = true; cut[r] = l == 0 ? 0 : Math.min(cut[r], cut[l - 1] + 1); } return cut[n - 1];
    }
}
```
