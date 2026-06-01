# LC Rotate Array First CSV

## Problem

Rotate comma-separated `nums` to the right by `k` steps and return the first element after rotation.

## Requirements

- `nums` is nonempty.
- `k >= 0`.

## Source

- Source: LeetCode problem `rotate-array`.
- URL: https://leetcode.com/problems/rotate-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcRotateArrayFirstCsv {
    public static int lc_rotate_array_first_csv(String nums, int k) {
        String[] p = nums.split(","); int n = p.length; k %= n; return Integer.parseInt(p[(n - k) % n]);
    }
}
```
