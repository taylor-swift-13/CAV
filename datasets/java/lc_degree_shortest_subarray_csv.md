# LC Degree Of Array Shortest Subarray CSV

## Problem

Return the shortest contiguous subarray length with the same degree as the whole array.

## Requirements

- `nums` is a nonempty comma-separated list of nonnegative integers less than 1000.

## Source

- Source: LeetCode problem `degree-of-an-array`.
- URL: https://leetcode.com/problems/degree-of-an-array/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcDegreeShortestSubarrayCsv {
    public static int lc_degree_shortest_subarray_csv(String nums) {
        int[] first = new int[1000], count = new int[1000]; java.util.Arrays.fill(first, -1); String[] p = nums.split(","); int degree = 0, best = 1000000;
        for (int i = 0; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (first[v] < 0) first[v] = i; count[v]++; int len = i - first[v] + 1; if (count[v] > degree) { degree = count[v]; best = len; } else if (count[v] == degree && len < best) best = len; } return best;
    }
}
```
