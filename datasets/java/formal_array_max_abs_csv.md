# formal_array_max_abs_csv

## Problem

Return the largest absolute value in nonempty comma-separated integer array `nums`.

## Requirements

- `nums` is nonempty and comma-separated.
- Negative values are allowed.
- Return the maximum absolute value.
- The absolute values fit in signed 32-bit integer range.

## Source

- Source: FormalBench-inspired program `array-max-abs`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FormalArrayMaxAbsCsv {
    public static int formal_array_max_abs_csv(String nums) {
        int best = 0;
        for (String p : nums.split(",")) { int v = Integer.parseInt(p); if (v < 0) v = -v; if (v > best) best = v; }
        return best;
    }
}
```
