# LC Jump Game CSV

## Problem

Return true if the last index is reachable from index `0` in comma-separated jump lengths.

## Requirements

- The empty string represents an empty array and returns false.
- Each value is nonnegative.

## Source

- Source: LeetCode problem `jump-game`.
- URL: https://leetcode.com/problems/jump-game/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcCanJumpCsv {
    public static boolean lc_can_jump_csv(String nums) {
        if (nums.isEmpty()) return false;
        String[] parts = nums.split(",");
        int reach = 0;
        for (int i = 0; i < parts.length; i++) { if (i > reach) return false; int v = Integer.parseInt(parts[i]); if (i + v > reach) reach = i + v; }
        return true;
    }
}
```
