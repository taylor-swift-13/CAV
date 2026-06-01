# LC Can Place Flowers Bool CSV

## Problem

Return true if `n` new flowers can be planted without adjacent flowers.

## Requirements

- `bed` is a comma-separated list of `0` and `1`.
- Existing flowers are not adjacent.

## Source

- Source: LeetCode problem `can-place-flowers`.
- URL: https://leetcode.com/problems/can-place-flowers/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcCanPlaceFlowersBoolCsv {
    public static boolean lc_can_place_flowers_bool_csv(String bed, int n) {
        String[] p = bed.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); for (int i = 0; i < a.length && n > 0; i++) if (a[i] == 0 && (i == 0 || a[i - 1] == 0) && (i == a.length - 1 || a[i + 1] == 0)) { a[i] = 1; n--; } return n <= 0;
    }
}
```
