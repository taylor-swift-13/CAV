# LC Majority Element II Count CSV

## Problem

Return how many distinct values appear more than `n/3` times.

## Requirements

- `nums` is a nonempty comma-separated list of signed integers.
- The answer is at most 2.

## Source

- Source: LeetCode problem `majority-element-ii`.
- URL: https://leetcode.com/problems/majority-element-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMajorityElementIiCountCsv {
    public static int lc_majority_element_ii_count_csv(String nums) {
        String[] p = nums.split(","); int ans = 0; for (int i = 0; i < p.length; i++) { boolean seen = false; for (int j = 0; j < i; j++) if (p[j].equals(p[i])) seen = true; if (!seen) { int cnt = 0; for (String x : p) if (x.equals(p[i])) cnt++; if (cnt > p.length / 3) ans++; } } return ans;
    }
}
```
