# LC Valid Perfect Square Bool

## Problem

Return true if `num` is a perfect square.

## Requirements

- `num > 0`.
- Use integer arithmetic only.

## Source

- Source: LeetCode problem `valid-perfect-square`.
- URL: https://leetcode.com/problems/valid-perfect-square/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcValidPerfectSquareBool {
    public static boolean lc_valid_perfect_square_bool(int num) {
        long l = 1, r = num; while (l <= r) { long m = (l + r) / 2, sq = m * m; if (sq == num) return true; if (sq < num) l = m + 1; else r = m - 1; } return false;
    }
}
```
