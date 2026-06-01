# LC Least Unique Integers After K Removals CSV

## Problem

Return the fewest distinct integers left after removing exactly `k` elements.

## Requirements

- `arr` is a comma-separated list of integers.

## Source

- Source: LeetCode problem `least-number-of-unique-integers-after-k-removals`.
- URL: https://leetcode.com/problems/least-number-of-unique-integers-after-k-removals/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLeastUniqueAfterKCsv {
    public static int lc_least_unique_after_k_csv(String arr, int k) {
        java.util.HashMap<Integer,Integer> map = new java.util.HashMap<Integer,Integer>(); for (String p : arr.split(",")) { int v = Integer.parseInt(p); map.put(v, map.getOrDefault(v, 0) + 1); } int[] freq = new int[map.size()]; int i = 0; for (int v : map.values()) freq[i++] = v; java.util.Arrays.sort(freq); int left = freq.length; for (int f : freq) { if (k < f) break; k -= f; left--; } return left;
    }
}
```
