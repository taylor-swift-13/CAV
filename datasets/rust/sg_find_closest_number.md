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

```rust
pub fn sg_find_closest_number(n: i32, nums: &[i32]) -> i32 {
    let mut ans = nums[0];
    let mut i = 1;
    while i < n {
        let a = if nums[i as usize] < 0 { -nums[i as usize] } else { nums[i as usize] };
        let b = if ans < 0 { -ans } else { ans };
        if a < b || (a == b && nums[i as usize] > ans) { ans = nums[i as usize]; }
        i += 1;
    }
    ans
}
```
