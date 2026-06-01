# LC Increasing Triplet Subsequence Bool CSV

## Problem

Return true if the array contains an increasing subsequence of length three.

## Requirements

- `nums` is a comma-separated list of signed integers.

## Source

- Source: LeetCode problem `increasing-triplet-subsequence`.
- URL: https://leetcode.com/problems/increasing-triplet-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcIncreasingTripletBoolCsv {
    public static boolean lc_increasing_triplet_bool_csv(String nums) {
        int first = Integer.MAX_VALUE, second = Integer.MAX_VALUE; for (String p : nums.split(",")) { int v = Integer.parseInt(p); if (v <= first) first = v; else if (v <= second) second = v; else return true; } return false;
    }
}
```
