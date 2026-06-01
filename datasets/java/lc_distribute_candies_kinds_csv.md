# LC Distribute Candies Kinds CSV

## Problem

Return the maximum number of candy kinds the sister can receive.

## Requirements

- `types` is a comma-separated list of integer candy types.
- The sister receives exactly half of the candies.

## Source

- Source: LeetCode problem `distribute-candies`.
- URL: https://leetcode.com/problems/distribute-candies/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcDistributeCandiesKindsCsv {
    public static int lc_distribute_candies_kinds_csv(String types) {
        String[] p = types.split(","); java.util.HashSet<Integer> set = new java.util.HashSet<Integer>(); for (String x : p) set.add(Integer.parseInt(x)); return Math.min(set.size(), p.length / 2);
    }
}
```
