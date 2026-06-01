# LC Contiguous Array Max Length CSV

## Problem

Return the maximum length of a contiguous subarray with equal numbers of 0 and 1.

## Requirements

- `nums` is a comma-separated binary array.

## Source

- Source: LeetCode problem `contiguous-array`.
- URL: https://leetcode.com/problems/contiguous-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcContiguousArrayMaxLenCsv {
    public static int lc_contiguous_array_max_len_csv(String nums) {
        String[] p = nums.split(","); java.util.HashMap<Integer,Integer> first = new java.util.HashMap<Integer,Integer>(); first.put(0, -1); int sum = 0, best = 0; for (int i = 0; i < p.length; i++) { sum += p[i].equals("1") ? 1 : -1; if (!first.containsKey(sum)) first.put(sum, i); else best = Math.max(best, i - first.get(sum)); } return best;
    }
}
```
