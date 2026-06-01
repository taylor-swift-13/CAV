# SpecGenBench Find Closest Number

## Problem

Return the array value closest to zero; if two values are equally close, return the larger value.

## Requirements

- `n > 0` and `nums` has at least `n` elements.
- Use only the first `n` values.
- Absolute values fit in signed 32-bit integer range.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/FindClosestNum`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/FindClosestNum/FindClosestNum.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class SgFindClosestNumber {
    public static int sg_find_closest_number(int n, int[] nums) {
        int ans = nums[0];
        for (int i = 1; i < n; i++) {
            int a = nums[i] < 0 ? -nums[i] : nums[i];
            int b = ans < 0 ? -ans : ans;
            if (a < b || (a == b && nums[i] > ans)) ans = nums[i];
        }
        return ans;
    }
}
```
