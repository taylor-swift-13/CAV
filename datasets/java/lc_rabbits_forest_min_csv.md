# LC Rabbits In Forest Minimum CSV

## Problem

Return the minimum number of rabbits consistent with the answers.

## Requirements

- `answers` is a comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `rabbits-in-forest`.
- URL: https://leetcode.com/problems/rabbits-in-forest/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcRabbitsForestMinCsv {
    public static int lc_rabbits_forest_min_csv(String answers) {
        java.util.HashMap<Integer,Integer> map = new java.util.HashMap<Integer,Integer>(); for (String p : answers.split(",")) { int v = Integer.parseInt(p); map.put(v, map.getOrDefault(v, 0) + 1); } int total = 0; for (int key : map.keySet()) { int group = key + 1, cnt = map.get(key); total += ((cnt + group - 1) / group) * group; } return total;
    }
}
```
