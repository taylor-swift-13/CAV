# LC Tuple With Same Product Count CSV

## Problem

Return how many ordered tuples have equal pair products.

## Requirements

- `nums` is a comma-separated list of distinct positive integers.

## Source

- Source: LeetCode problem `tuple-with-same-product`.
- URL: https://leetcode.com/problems/tuple-with-same-product/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcTupleSameProductCountCsv {
    public static int lc_tuple_same_product_count_csv(String nums) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); java.util.ArrayList<Integer> prod = new java.util.ArrayList<Integer>(); for (int i = 0; i < a.length; i++) for (int j = i + 1; j < a.length; j++) prod.add(a[i] * a[j]); int ans = 0; for (int i = 0; i < prod.size(); i++) for (int j = i + 1; j < prod.size(); j++) if (prod.get(i).equals(prod.get(j))) ans += 8; return ans;
    }
}
```
