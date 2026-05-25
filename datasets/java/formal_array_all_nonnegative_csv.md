# formal_array_all_nonnegative_csv

## Problem

Return true if every value in comma-separated integer array `nums` is nonnegative.

## Requirements

- The empty array is considered all nonnegative.
- Values are comma-separated with no spaces.
- Zero is nonnegative.
- Return false if any value is below zero.

## Source

- Source: FormalBench-inspired program `array-all-nonnegative`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FormalArrayAllNonnegativeCsv {
    public static boolean formal_array_all_nonnegative_csv(String nums) {
        if (nums.isEmpty()) return true;
        for (String p : nums.split(",")) if (Integer.parseInt(p) < 0) return false;
        return true;
    }
}
```
