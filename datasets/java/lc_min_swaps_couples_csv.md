# LC Couples Holding Hands Min Swaps CSV

## Problem

Return the minimum adjacent-seat swaps needed so every couple sits together.

## Requirements

- `row` is a comma-separated seating arrangement.
- Couples are `(0,1)`, `(2,3)`, and so on.

## Source

- Source: LeetCode problem `couples-holding-hands`.
- URL: https://leetcode.com/problems/couples-holding-hands/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMinSwapsCouplesCsv {
    public static int lc_min_swaps_couples_csv(String row) {
        String[] p = row.split(","); int[] a = new int[p.length], pos = new int[p.length]; for (int i = 0; i < p.length; i++) { a[i] = Integer.parseInt(p[i]); pos[a[i]] = i; } int swaps = 0; for (int seat = 0; seat < a.length; seat += 2) { int mate = a[seat] ^ 1; if (a[seat + 1] != mate) { int mpos = pos[mate], other = a[seat + 1]; a[mpos] = other; pos[other] = mpos; a[seat + 1] = mate; pos[mate] = seat + 1; swaps++; } } return swaps;
    }
}
```
