# array_is_sorted_csv

## Problem

Return true if comma-separated integer string `nums` is sorted in nondecreasing order.

## Requirements

- `nums` is comma-separated base-10 integers with no spaces.
- The empty string is considered sorted.
- Duplicates are allowed.
- Return false on the first adjacent decrease.

## Source

- Source: FormalBench-inspired program `array-sorted`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ArrayIsSortedCsv {
    public static boolean array_is_sorted_csv(String nums) {
        if (nums.isEmpty()) return true;
        String[] p = nums.split(",");
        int prev = Integer.parseInt(p[0]);
        for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (v < prev) return false; prev = v; }
        return true;
    }
}
```
