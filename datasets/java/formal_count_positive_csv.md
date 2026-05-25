# formal_count_positive_csv

## Problem

Return how many values in comma-separated integer array `nums` are strictly positive.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string represents an empty array.
- Zero is not positive.
- Return the count of strictly positive values.

## Source

- Source: FormalBench-inspired program `count-positive`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FormalCountPositiveCsv {
    public static int formal_count_positive_csv(String nums) {
        if (nums.isEmpty()) return 0;
        int count = 0;
        for (String p : nums.split(",")) if (Integer.parseInt(p) > 0) count++;
        return count;
    }
}
```
